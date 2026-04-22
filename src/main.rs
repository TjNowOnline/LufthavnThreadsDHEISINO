
// Bagagesorteringssystem - Lufthavn Simulation i Rust
// Bruger tråde (std::thread) og synkronisering (Arc<Mutex<T>>)
// for at simulere et virkeligt bagageflow gennem en lufthavn.


use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock};
use std::thread;
use std::time::{Duration, Instant};

use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode, KeyEventKind},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::CrosstermBackend,
    layout::{Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, Paragraph, Wrap},
    Frame, Terminal as RatatuiTerminal,
};


// SIMPEL TILFÆLDIG TAL-GENERATOR (LCG)
// Vi bruger ingen eksterne crates - kun std.
// LCG = Linear Congruential Generator: hurtig, god nok til simulation.
// Hver tråd får sin egen instans baseret på tråd-ID + tidspunkt.


/// Trådsikker tilfældig tal-generator baseret på LCG-algoritmen.
/// Seed opdateres atomart ved hvert kald - ingen Mutex nødvendig!
struct Rng {
    // AtomicU64 som seed - fetch_update giver os race-free opdatering
    tilstand: AtomicU64,
}

impl Rng {
    fn ny(frø: u64) -> Self {
        Rng { tilstand: AtomicU64::new(frø) }
    }

    /// Returnerer et tilfældigt u64 via LCG
    /// Konstanter fra Knuth
    fn næste(&self) -> u64 {
        // fetch_update: læs → beregn → skriv atomart
        self.tilstand.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |s| {
            Some(s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407))
        }).unwrap()
    }

    /// Returnerer et tal i intervallet [min, max] (begge inklusive)
    fn interval(&self, min: u64, max: u64) -> u64 {
        min + (self.næste() % (max - min + 1))
    }

    /// Tilfældig Duration i millisekunder inden for [min_ms, max_ms]
    fn varighed_ms(&self, min_ms: u64, max_ms: u64) -> Duration {
        Duration::from_millis(self.interval(min_ms, max_ms))
    }
}

/// Opretter en unik RNG baseret på tråd-ID og nuværende tid.
/// Kaldes i starten af hver tråd for at give forskelligt flow.
fn ny_rng() -> Rng {
    // Bland tråd-ID (ikke direkte tilgængeligt i std) med Instant
    // for at få et varieret frø per tråd
    let tid_ns = Instant::now().elapsed().subsec_nanos() as u64;
    // AtomicU64 der tæller op globalt - giver unik offset per kald
    static TÆLLER: AtomicU64 = AtomicU64::new(1);
    let unik = TÆLLER.fetch_add(1, Ordering::Relaxed);
    Rng::ny(tid_ns.wrapping_mul(2654435761).wrapping_add(unik * 1234567891))
}

// KONSTANTER - faste grænser der simulerer fysiske begrænsninger

// Maks antal bagager i sorteringsanlæggets buffer ad gangen
const SORTERING_BUFFER_KAPACITET: usize = 20;
// Maks antal bagager i en gate-terminal buffer ad gangen
const TERMINAL_BUFFER_KAPACITET: usize = 30;
// Maks antal bagager en skranke kan have klar i sin kø
const SKRANKE_BUFFER_KAPACITET: usize = 10;

// ----------------------------------------------------------------
// DATASTRUKTURER
// ----------------------------------------------------------------

/// En passagerreservation fra reservationssystemet.
/// I virkeligheden ville dette komme fra en database eller API,
/// men her har vi det som statiske data - nemmere at forstå.
#[derive(Debug, Clone)]
struct Reservation {
    passager_nr: u32,
    #[allow(dead_code)]
    navn: String,
    flyafgang: String, // f.eks. "SK202"
}

/// En post i flyveplanen. Flyplanen kan opdateres under kørslen
/// via en separat tråd - derfor er den bag en RwLock, så mange
/// tråde kan læse samtidig, men kun én kan skrive ad gangen.
#[derive(Debug, Clone)]
struct Flyafgang {
    flight_nr: String,
    terminal_nr: u32, // Gate-nummer
    afgang_tid: String,
    aktiv: bool, // Er gaten åben for boarding?
}

/// Repræsenterer et stykke bagage i systemet.
/// Holder styr på hele rejsen fra check-in til gate.
#[derive(Debug, Clone)]
struct Bagage {
    bagage_nr: String,
    passager_nr: u32,
    flight_nr: String,
    check_in_skranke: u32,
    tidsstempel_check_in: Option<Instant>,
    tidsstempel_sortering_ind: Option<Instant>,
    tidsstempel_sortering_ud: Option<Instant>,
    tidsstempel_terminal: Option<Instant>,
}

impl Bagage {
    fn ny(bagage_nr: &str, passager_nr: u32, flight_nr: &str, skranke_id: u32) -> Self {
        Bagage {
            bagage_nr: bagage_nr.to_string(),
            passager_nr,
            flight_nr: flight_nr.to_string(),
            check_in_skranke: skranke_id,
            tidsstempel_check_in: None,
            tidsstempel_sortering_ind: None,
            tidsstempel_sortering_ud: None,
            tidsstempel_terminal: None,
        }
    }
}

/// Statistik til throughput-måling - deles mellem alle tråde
/// via atomare tællere (AtomicU64) for at undgå låse på hot-path.
/// Atomic operationer er hurtigere end Mutex til simple tælle-operationer!
#[derive(Debug)]
struct ThroughputStatistik {
    bagage_behandlet_total: AtomicU64,
    total_ventetid_ms: AtomicU64,      // samlet ventetid i ms
    sortering_behandlet: AtomicU64,
    terminaler_modtaget: AtomicU64,
    start_tid: Mutex<Option<Instant>>,
}

impl ThroughputStatistik {
    fn ny() -> Self {
        ThroughputStatistik {
            bagage_behandlet_total: AtomicU64::new(0),
            total_ventetid_ms: AtomicU64::new(0),
            sortering_behandlet: AtomicU64::new(0),
            terminaler_modtaget: AtomicU64::new(0),
            start_tid: Mutex::new(None),
        }
    }

    fn start(&self) {
        let mut t = self.start_tid.lock().unwrap();
        *t = Some(Instant::now());
    }

    /// Beregner throughput i enheder per sekund
    fn throughput(&self) -> f64 {
        let t = self.start_tid.lock().unwrap();
        if let Some(start) = *t {
            let sek = start.elapsed().as_secs_f64();
            if sek > 0.0 {
                return self.bagage_behandlet_total.load(Ordering::Relaxed) as f64 / sek;
            }
        }
        0.0
    }

    /// Gennemsnitlig ventetid per bagage i millisekunder
    fn gns_ventetid_ms(&self) -> f64 {
        let total = self.bagage_behandlet_total.load(Ordering::Relaxed);
        if total == 0 {
            return 0.0;
        }
        self.total_ventetid_ms.load(Ordering::Relaxed) as f64 / total as f64
    }
}

// ----------------------------------------------------------------
// CENTRAL SERVER - overvåger hele systemet
// ----------------------------------------------------------------

/// Den centrale server holder styr på:
/// - Reservationer (statiske ved start, men kan udvides)
/// - Flyveplanen (kan opdateres via tråd eller brugerinput)
/// - En global log over alle hændelser
/// - Statistik for throughput-måling
///
/// Arc<RwLock<...>> bruges til flyveplanen fordi mange tråde
/// læser den (for at finde gate-nummer), men sjældent opdateres.
/// RwLock er perfekt her - bedre end Mutex til read-heavy data!
struct CentralServer {
    reservationer: Vec<Reservation>,
    flyveplan: Arc<RwLock<Vec<Flyafgang>>>,
    // Global hændelseslog - alle tråde skriver hertil
    hændelses_log: Arc<Mutex<Vec<String>>>,
    // Log-fil til persistens
    log_fil: Arc<Mutex<File>>,
    statistik: Arc<ThroughputStatistik>,
}

impl CentralServer {
    fn ny(log_sti: &str) -> Self {
        // Åbn (eller opret) log-filen - append mode så vi ikke mister data
        let fil = OpenOptions::new()
            .create(true)
            .append(true)
            .open(log_sti)
            .expect("Kunne ikke åbne log-fil");

        CentralServer {
            reservationer: Vec::new(),
            flyveplan: Arc::new(RwLock::new(Vec::new())),
            hændelses_log: Arc::new(Mutex::new(Vec::new())),
            log_fil: Arc::new(Mutex::new(fil)),
            statistik: Arc::new(ThroughputStatistik::ny()),
        }
    }

    /// Indlæser reservationer fra en tekstfil (CSV-lignende format)
    /// Format per linje: passager_nr,navn,flyafgang
    fn indlæs_reservationer_fra_fil(&mut self, sti: &str) {
        match File::open(sti) {
            Ok(fil) => {
                let læser = BufReader::new(fil);
                for linje in læser.lines().flatten() {
                    let dele: Vec<&str> = linje.split(',').collect();
                    if dele.len() == 3 {
                        if let Ok(nr) = dele[0].trim().parse::<u32>() {
                            self.reservationer.push(Reservation {
                                passager_nr: nr,
                                navn: dele[1].trim().to_string(),
                                flyafgang: dele[2].trim().to_string(),
                            });
                        }
                    }
                }
            }
            Err(_) => {
                self.opret_standard_reservationer();
            }
        }
    }

    /// Statiske testdata - som om vi har hardkodet dem i systemet.
    /// I en rigtig implementering ville disse komme fra en database.
    fn opret_standard_reservationer(&mut self) {
        self.reservationer = vec![
            Reservation { passager_nr: 1001, navn: "Anders Andersen".to_string(),  flyafgang: "SK202".to_string() },
            Reservation { passager_nr: 1002, navn: "Bente Bentsen".to_string(),    flyafgang: "SK202".to_string() },
            Reservation { passager_nr: 1003, navn: "Carl Carlsen".to_string(),      flyafgang: "DY415".to_string() },
            Reservation { passager_nr: 1004, navn: "Dorthe Dorthesen".to_string(), flyafgang: "DY415".to_string() },
            Reservation { passager_nr: 1005, navn: "Erik Eriksen".to_string(),      flyafgang: "TK791".to_string() },
            Reservation { passager_nr: 1006, navn: "Freja Frejsen".to_string(),     flyafgang: "SK202".to_string() },
            Reservation { passager_nr: 1007, navn: "Gitte Gittesen".to_string(),    flyafgang: "TK791".to_string() },
            Reservation { passager_nr: 1008, navn: "Hans Hansen".to_string(),       flyafgang: "DY415".to_string() },
            Reservation { passager_nr: 1009, navn: "Ida Idsen".to_string(),         flyafgang: "SK202".to_string() },
            Reservation { passager_nr: 1010, navn: "Jens Jensen".to_string(),       flyafgang: "TK791".to_string() },
            Reservation { passager_nr: 1011, navn: "Karen Karsen".to_string(),      flyafgang: "SK202".to_string() },
            Reservation { passager_nr: 1012, navn: "Lars Larsen".to_string(),       flyafgang: "DY415".to_string() },
        ];
    }

    /// Opretter standard flyveplan
    fn opret_standard_flyveplan(&self) {
        let mut plan = self.flyveplan.write().unwrap();
        *plan = vec![
            Flyafgang { flight_nr: "SK202".to_string(), terminal_nr: 1, afgang_tid: "10:30".to_string(), aktiv: true },
            Flyafgang { flight_nr: "DY415".to_string(), terminal_nr: 2, afgang_tid: "11:15".to_string(), aktiv: true },
            Flyafgang { flight_nr: "TK791".to_string(), terminal_nr: 3, afgang_tid: "12:00".to_string(), aktiv: true },
        ];
    }

    /// Finder gate-nummer for et fly - bruges af sorteringsanlægget
    /// Vi bruger read() her - mange tråde kan slå op samtidig!
    #[allow(dead_code)]
    fn find_terminal_for_fly(&self, flight_nr: &str) -> Option<u32> {
        let plan = self.flyveplan.read().unwrap();
        plan.iter()
            .find(|f| f.flight_nr == flight_nr && f.aktiv)
            .map(|f| f.terminal_nr)
    }

    /// Logger en hændelse til både skærm, intern log og fil
    #[allow(dead_code)]
    fn log(&self, besked: &str) {
        let tidsstemplet = format!("[LOG] {}", besked);
        // Skriv til fil - lås fil-mutex kort
        {
            let mut fil = self.log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", tidsstemplet);
        }
        // Gem i intern log
        {
            let mut log = self.hændelses_log.lock().unwrap();
            log.push(tidsstemplet);
        }
    }

    /// Finder flyafgang for en passager
    #[allow(dead_code)]
    fn find_flyafgang(&self, passager_nr: u32) -> Option<String> {
        self.reservationer
            .iter()
            .find(|r| r.passager_nr == passager_nr)
            .map(|r| r.flyafgang.clone())
    }
}

// ----------------------------------------------------------------
// SKRANKE (CHECK-IN COUNTER)
// ----------------------------------------------------------------

/// En skranke modtager passagerer og registrerer deres bagage.
/// Hver skranke kører i sin egen tråd og sender bagage videre
/// til sorteringsanlæggets indgangsbuffer via en delt Arc<Mutex<...>>.
///
/// is_åben styres atomart - vi behøver ikke låse hele strukturen
/// bare for at tjekke om skranken er åben. AtomicBool er perfekt til dette!
struct Skranke {
    id: u32,
    // AtomicBool til åben/lukket status - ingen Mutex nødvendig for denne bool!
    is_åben: Arc<AtomicBool>,
    // Buffer af bagage klar til at blive sendt til sortering
    // Kapacitet begrænset til SKRANKE_BUFFER_KAPACITET
    udgående_buffer: Arc<Mutex<Vec<Bagage>>>,
    // Sorteringsanlæggets indgangsbuffer - deles mellem ALLE skranker
    sortering_ind: Arc<(Mutex<Vec<Bagage>>, Condvar)>,
    // Fælles log
    hændelses_log: Arc<Mutex<Vec<String>>>,
    log_fil: Arc<Mutex<File>>,
    statistik: Arc<ThroughputStatistik>,
}

impl Skranke {
    fn ny(
        id: u32,
        sortering_ind: Arc<(Mutex<Vec<Bagage>>, Condvar)>,
        hændelses_log: Arc<Mutex<Vec<String>>>,
        log_fil: Arc<Mutex<File>>,
        statistik: Arc<ThroughputStatistik>,
    ) -> Self {
        Skranke {
            id,
            is_åben: Arc::new(AtomicBool::new(false)),
            udgående_buffer: Arc::new(Mutex::new(Vec::new())),
            sortering_ind,
            hændelses_log,
            log_fil,
            statistik,
        }
    }

    /// Logger en besked fra denne skranke
    fn log(&self, besked: &str) {
        let linje = format!("[Skranke {}] {}", self.id, besked);
        {
            let mut fil = self.log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", linje);
        }
        let mut log = self.hændelses_log.lock().unwrap();
        log.push(linje);
    }

    /// Åbn skranken - sæt atomart flag
    fn åbn(&self) {
        self.is_åben.store(true, Ordering::SeqCst);
        self.log("Skranke ÅBNET.");
    }

    /// Luk skranken
    fn luk(&self) {
        self.is_åben.store(false, Ordering::SeqCst);
        self.log("Skranke LUKKET.");
    }

    /// Modtager og registrerer en bagageenhed.
    /// Simulerer den realistiske tid det tager at tjekke pas,
    /// veje kufferten og printe stregkode: 300-900ms (skaleret til ms).
    /// Med 1 skranke og mange passagerer → synlig kø!
    fn modtag_bagage(&self, mut bagage: Bagage, rng: &Rng) -> bool {
        if !self.is_åben.load(Ordering::SeqCst) {
            self.log(&format!(
                "Afviste bagage {} - skranken er lukket!",
                bagage.bagage_nr
            ));
            return false;
        }

        // Realistisk check-in tid: pas-tjek + vejning + stregkode-print
        // 300-900ms simuleret (i virkeligheden 1-3 minutter per passager)
        let checkin_tid = rng.varighed_ms(300, 900);
        self.log(&format!(
            "Behandler passager {} - pas & vejning... ({}ms)",
            bagage.passager_nr,
            checkin_tid.as_millis()
        ));
        thread::sleep(checkin_tid);

        // Registrer tidsstempel for check-in (efter behandling)
        bagage.tidsstempel_check_in = Some(Instant::now());
        bagage.check_in_skranke = self.id;

        let mut buf = self.udgående_buffer.lock().unwrap();
        if buf.len() >= SKRANKE_BUFFER_KAPACITET {
            self.log(&format!(
                "⚠ Buffer fuld! Kan ikke modtage bagage {}. Kø: {}/{}",
                bagage.bagage_nr,
                buf.len(),
                SKRANKE_BUFFER_KAPACITET
            ));
            return false;
        }

        self.log(&format!(
            "✓ Registrerede bagage {} for passager {} (fly: {})",
            bagage.bagage_nr, bagage.passager_nr, bagage.flight_nr
        ));
        buf.push(bagage);
        true
    }

    /// Sender al bagage fra lokal buffer videre til sorteringsanlægget.
    /// Bruger Condvar til at signalere sorteringsanlægget om ny bagage.
    /// Dette undgår busy-waiting - tråden sover indtil der er plads!
    fn send_til_sortering(&self) {
        let mut lokal_buf = self.udgående_buffer.lock().unwrap();
        if lokal_buf.is_empty() {
            return;
        }

        let (sortering_lås, condvar) = &*self.sortering_ind;

        // Vi prøver at sende hver bagageenhed - venter hvis bufferen er fuld
        while let Some(bagage) = lokal_buf.first().cloned() {
            let ventetid_start = Instant::now();

            let mut sort_buf = sortering_lås.lock().unwrap();
            // Vent (med condvar) hvis sorteringsbufferen er fuld
            // condvar.wait() frigiver låsen mens vi venter - smart!
            while sort_buf.len() >= SORTERING_BUFFER_KAPACITET {
                self.log(&format!(
                    "⚠ KØ: Venter på plads i sorteringsbuffer ({}/{}) - sortering kan ikke følge med!",
                    sort_buf.len(),
                    SORTERING_BUFFER_KAPACITET
                ));
                sort_buf = condvar.wait(sort_buf).unwrap();
            }

            let ventetid_ms = ventetid_start.elapsed().as_millis() as u64;
            self.statistik.total_ventetid_ms.fetch_add(ventetid_ms, Ordering::Relaxed);

            // Log kø-niveau for at gøre flaskehalsen synlig
            let kø_niveau = sort_buf.len() + 1;
            let kø_indikator = "█".repeat(kø_niveau).to_string()
                + &"░".repeat(SORTERING_BUFFER_KAPACITET.saturating_sub(kø_niveau));
            self.log(&format!(
                "→ Sortering [{}] {}/{} (ventetid: {}ms)",
                kø_indikator, kø_niveau, SORTERING_BUFFER_KAPACITET, ventetid_ms
            ));

            sort_buf.push(bagage);
            condvar.notify_one();
            lokal_buf.remove(0);

            self.statistik.bagage_behandlet_total.fetch_add(1, Ordering::Relaxed);
        }
    }
}

// ----------------------------------------------------------------
// SORTERINGSANLÆG
// ----------------------------------------------------------------

/// Sorteringsanlægget er systemets hjerte - det modtager bagage
/// fra alle skranker og sorterer dem til den rigtige gate/terminal.
///
/// Vi bruger et producer-consumer mønster med Condvar:
/// - Skranker er producers (fylder ind-bufferen)
/// - Sortering er consumer (tømmer ind-bufferen, fylder terminal-buffere)
///
/// Condvar er perfekt her! I stedet for at sorteringen spinner
/// og spilder CPU mens den venter på bagage, sover tråden og
/// vågner kun når der er noget at gøre.
struct Sorteringsanlæg {
    // Indgangsbuffer - deles med alle skranker
    ind_buffer: Arc<(Mutex<Vec<Bagage>>, Condvar)>,
    // Terminal-buffere - én per gate, keyed by terminal_nr
    terminal_buffere: Arc<Mutex<HashMap<u32, Arc<(Mutex<Vec<Bagage>>, Condvar)>>>>,
    // Flyveplan til at slå gate op for et fly
    flyveplan: Arc<RwLock<Vec<Flyafgang>>>,
    hændelses_log: Arc<Mutex<Vec<String>>>,
    log_fil: Arc<Mutex<File>>,
    #[allow(dead_code)]
    statistik: Arc<ThroughputStatistik>,
    // Stop-signal til tråden - AtomicBool = ingen Mutex for dette simple flag
    stop_signal: Arc<AtomicBool>,
}

impl Sorteringsanlæg {
    fn ny(
        ind_buffer: Arc<(Mutex<Vec<Bagage>>, Condvar)>,
        flyveplan: Arc<RwLock<Vec<Flyafgang>>>,
        hændelses_log: Arc<Mutex<Vec<String>>>,
        log_fil: Arc<Mutex<File>>,
        statistik: Arc<ThroughputStatistik>,
    ) -> Self {
        Sorteringsanlæg {
            ind_buffer,
            terminal_buffere: Arc::new(Mutex::new(HashMap::new())),
            flyveplan,
            hændelses_log,
            log_fil,
            statistik,
            stop_signal: Arc::new(AtomicBool::new(false)),
        }
    }

    fn log(&self, besked: &str) {
        let linje = format!("[Sortering] {}", besked);
        {
            let mut fil = self.log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", linje);
        }
        let mut log = self.hændelses_log.lock().unwrap();
        log.push(linje);
    }

    /// Registrerer en terminal-buffer - kaldes når en gate åbner
    fn registrér_terminal(&self, terminal_nr: u32, buffer: Arc<(Mutex<Vec<Bagage>>, Condvar)>) {
        let mut buffere = self.terminal_buffere.lock().unwrap();
        buffere.insert(terminal_nr, buffer);
        self.log(&format!("Terminal {} registreret i sortering.", terminal_nr));
    }

    /// Finder gate-nummer for et fly via flyveplanen
    #[allow(dead_code)]
    fn find_terminal(&self, flight_nr: &str) -> Option<u32> {
        let plan = self.flyveplan.read().unwrap();
        plan.iter()
            .find(|f| f.flight_nr == flight_nr && f.aktiv)
            .map(|f| f.terminal_nr)
    }

    /// Starter sorteringsanlæggets behandlingstråd.
    /// Tråden kører i en løkke: venter på bagage → sorterer → sender til gate.
    /// Bruger en timeout på wait_timeout så vi kan tjekke stop-signalet.
    fn start_sortering_tråd(
        ind_buffer: Arc<(Mutex<Vec<Bagage>>, Condvar)>,
        terminal_buffere: Arc<Mutex<HashMap<u32, Arc<(Mutex<Vec<Bagage>>, Condvar)>>>>,
        flyveplan: Arc<RwLock<Vec<Flyafgang>>>,
        hændelses_log: Arc<Mutex<Vec<String>>>,
        log_fil: Arc<Mutex<File>>,
        statistik: Arc<ThroughputStatistik>,
        stop_signal: Arc<AtomicBool>,
    ) -> thread::JoinHandle<()> {
        thread::spawn(move || {
            // Logger hjælpefunktion som closure
            let log = |besked: &str| {
                let linje = format!("[Sortering] {}", besked);
                {
                    let mut fil = log_fil.lock().unwrap();
                    let _ = writeln!(fil, "{}", linje);
                }
                let mut l = hændelses_log.lock().unwrap();
                l.push(linje);
            };

            log("Sorteringstråd startet - venter på bagage...");

            loop {
                // Tjek stop-signal INDEN vi låser
                if stop_signal.load(Ordering::SeqCst) {
                    log("Stop-signal modtaget. Afslutter sorteringstråd.");
                    break;
                }

                let bagage_til_behandling: Option<Bagage> = {
                    let (lås, condvar) = &*ind_buffer;
                    let mut buf = lås.lock().unwrap();

                    // Vent med timeout - så vi kan tjekke stop-signalet
                    // wait_timeout returnerer selv om ingen notificerer - det er OK!
                    let (buf2, _timeout) = condvar
                        .wait_timeout(buf, Duration::from_millis(200))
                        .unwrap();
                    buf = buf2;

                    if buf.is_empty() {
                        None
                    } else {
                        // Tag første bagage fra bufferen
                        let mut b = buf.remove(0);
                        b.tidsstempel_sortering_ind = Some(Instant::now());
                        // Notificér skranker om at der nu er plads
                        condvar.notify_all();
                        Some(b)
                    }
                };

                if let Some(mut bagage) = bagage_til_behandling {
                    // Realistisk transportbånd-tid: mekanisk forsinkelse + stregkode-læsning
                    // 80-200ms - varierer pga. båndhastighed og scan-forsøg
                    let sort_rng = ny_rng();
                    let sort_tid = sort_rng.varighed_ms(80, 200);
                    thread::sleep(sort_tid);
                    bagage.tidsstempel_sortering_ud = Some(Instant::now());

                    // Find korrekt terminal for dette fly
                    let terminal_nr = {
                        let plan = flyveplan.read().unwrap();
                        plan.iter()
                            .find(|f| f.flight_nr == bagage.flight_nr && f.aktiv)
                            .map(|f| f.terminal_nr)
                    };

                    match terminal_nr {
                        Some(t_nr) => {
                            log(&format!(
                                "Sorterede bagage {} → Terminal {} (fly: {})",
                                bagage.bagage_nr, t_nr, bagage.flight_nr
                            ));

                            // Send til terminal-buffer
                            let term_buf_opt = {
                                let buffere = terminal_buffere.lock().unwrap();
                                buffere.get(&t_nr).cloned()
                            };

                            if let Some(term_arc) = term_buf_opt {
                                let (t_lås, t_condvar) = &*term_arc;
                                let mut t_buf = t_lås.lock().unwrap();
                                // Vent hvis terminal-buffer er fuld
                                while t_buf.len() >= TERMINAL_BUFFER_KAPACITET {
                                    log(&format!(
                                        "Terminal {}-buffer fuld - venter...",
                                        t_nr
                                    ));
                                    t_buf = t_condvar.wait(t_buf).unwrap();
                                }
                                t_buf.push(bagage);
                                t_condvar.notify_one();
                                statistik.sortering_behandlet.fetch_add(1, Ordering::Relaxed);
                            } else {
                                log(&format!(
                                    "ADVARSEL: Ingen terminal {} registreret! Bagage {} mistet.",
                                    t_nr, bagage.bagage_nr
                                ));
                            }
                        }
                        None => {
                            log(&format!(
                                "ADVARSEL: Intet fly {} fundet i flyveplan! Bagage {} mistet.",
                                bagage.flight_nr, bagage.bagage_nr
                            ));
                        }
                    }
                }
            }

            log("Sorteringstråd afsluttet.");
        })
    }
}

// ----------------------------------------------------------------
// TERMINAL (GATE)
// ----------------------------------------------------------------

/// En terminal (gate) modtager sorteret bagage og loader den på flyet.
/// Terminalen kører i sin egen tråd og overvåger sin buffer.
/// Gaten kan åbnes og lukkes - ved lukning afvises ny bagage.
struct Terminal {
    id: u32,
    flight_nr: String,
    is_åben: Arc<AtomicBool>,
    // Buffer deles med sorteringsanlægget via Arc
    buffer: Arc<(Mutex<Vec<Bagage>>, Condvar)>,
    loadet_bagage: Arc<Mutex<Vec<String>>>, // bagage_nr'e der er loaded
    hændelses_log: Arc<Mutex<Vec<String>>>,
    log_fil: Arc<Mutex<File>>,
    #[allow(dead_code)]
    statistik: Arc<ThroughputStatistik>,
    stop_signal: Arc<AtomicBool>,
}

impl Terminal {
    fn ny(
        id: u32,
        flight_nr: &str,
        hændelses_log: Arc<Mutex<Vec<String>>>,
        log_fil: Arc<Mutex<File>>,
        statistik: Arc<ThroughputStatistik>,
    ) -> Self {
        Terminal {
            id,
            flight_nr: flight_nr.to_string(),
            is_åben: Arc::new(AtomicBool::new(false)),
            buffer: Arc::new((Mutex::new(Vec::new()), Condvar::new())),
            loadet_bagage: Arc::new(Mutex::new(Vec::new())),
            hændelses_log,
            log_fil,
            statistik,
            stop_signal: Arc::new(AtomicBool::new(false)),
        }
    }

    fn log(&self, besked: &str) {
        let linje = format!("[Terminal {}|{}] {}", self.id, self.flight_nr, besked);
        {
            let mut fil = self.log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", linje);
        }
        let mut log = self.hændelses_log.lock().unwrap();
        log.push(linje);
    }

    fn åbn(&self) {
        self.is_åben.store(true, Ordering::SeqCst);
        self.log("Terminal ÅBNET - klar til boarding.");
    }

    #[allow(dead_code)]
    fn luk(&self) {
        self.is_åben.store(false, Ordering::SeqCst);
        self.log("Terminal LUKKET.");
    }

    /// Starter terminal-tråden.
    /// Tråden venter på bagage i bufferen (via Condvar) og
    /// simulerer at loade bagagen på flyet.
    fn start_terminal_tråd(
        terminal_id: u32,
        flight_nr: String,
        is_åben: Arc<AtomicBool>,
        buffer: Arc<(Mutex<Vec<Bagage>>, Condvar)>,
        loadet_bagage: Arc<Mutex<Vec<String>>>,
        hændelses_log: Arc<Mutex<Vec<String>>>,
        log_fil: Arc<Mutex<File>>,
        statistik: Arc<ThroughputStatistik>,
        stop_signal: Arc<AtomicBool>,
    ) -> thread::JoinHandle<()> {
        thread::spawn(move || {
            let log = |besked: &str| {
                let linje = format!("[Terminal {}|{}] {}", terminal_id, flight_nr, besked);
                {
                    let mut fil = log_fil.lock().unwrap();
                    let _ = writeln!(fil, "{}", linje);
                }
                let mut l = hændelses_log.lock().unwrap();
                l.push(linje);
            };

            log("Terminal-tråd startet.");

            loop {
                if stop_signal.load(Ordering::SeqCst) {
                    log("Stop-signal. Afslutter terminal-tråd.");
                    break;
                }

                if !is_åben.load(Ordering::SeqCst) {
                    // Terminalen er lukket - sov lidt og tjek igen
                    thread::sleep(Duration::from_millis(100));
                    continue;
                }

                let bagage: Option<Bagage> = {
                    let (lås, condvar) = &*buffer;
                    let buf = lås.lock().unwrap();
                    let (mut buf2, _) = condvar
                        .wait_timeout(buf, Duration::from_millis(200))
                        .unwrap();
                    if buf2.is_empty() {
                        None
                    } else {
                        let mut b = buf2.remove(0);
                        b.tidsstempel_terminal = Some(Instant::now());
                        condvar.notify_all();
                        Some(b)
                    }
                };

                if let Some(b) = bagage {
                    // Realistisk terminal-loading tid:
                    // Transportbånd fra sortering til flyets lastrum - 40-120ms
                    // Varierer pga. gate-afstand og lastrum-placering
                    let term_rng = ny_rng();
                    let load_tid = term_rng.varighed_ms(40, 120);
                    thread::sleep(load_tid);

                    log(&format!(
                        "✈ Loadede bagage {} på fly {} (passager: {}, loadtid: {}ms)",
                        b.bagage_nr, b.flight_nr, b.passager_nr, load_tid.as_millis()
                    ));

                    // Beregn total rejsetid for bagagen
                    if let (Some(ind), Some(ud)) = (b.tidsstempel_check_in, b.tidsstempel_terminal) {
                        let total_ms = ud.duration_since(ind).as_millis();
                        // Marker lange rejsetider - tegn på kø-problemer
                        let hastighed = if total_ms > 2000 { "⚠ LANGSOM" } else { "✓ OK" };
                        log(&format!(
                            "Bagage {} total rejsetid: {}ms [{}]",
                            b.bagage_nr, total_ms, hastighed
                        ));
                    }

                    let mut loaded = loadet_bagage.lock().unwrap();
                    loaded.push(b.bagage_nr.clone());
                    statistik.terminaler_modtaget.fetch_add(1, Ordering::Relaxed);
                }
            }

            log("Terminal-tråd afsluttet.");
        })
    }
}

// ----------------------------------------------------------------
// FLYVEPLAN OPDATERINGS-TRÅD
// ----------------------------------------------------------------

/// Simulerer at flyplanen opdateres løbende (nye fly, ændringer, osv.)
/// I virkeligheden ville dette komme fra et eksternt system.
/// Tråden bruger write()-låsen på RwLock - blokerer alle læsere kortvarigt.
fn start_flyveplan_opdaterings_tråd(
    flyveplan: Arc<RwLock<Vec<Flyafgang>>>,
    log_fil: Arc<Mutex<File>>,
    stop_signal: Arc<AtomicBool>,
) -> thread::JoinHandle<()> {
    thread::spawn(move || {
        // Vent lidt inden vi "opdaterer" planen for at simulere et real-world scenarie
        thread::sleep(Duration::from_millis(500));

        if stop_signal.load(Ordering::SeqCst) {
            return;
        }

        // Tilføj et ekstra fly til planen (simulerer en sen tilføjelse)
        {
            let mut plan = flyveplan.write().unwrap();
            plan.push(Flyafgang {
                flight_nr: "EK007".to_string(),
                terminal_nr: 4,
                afgang_tid: "13:45".to_string(),
                aktiv: true,
            });
            let linje = "[Flyveplan] Tilføjede ny afgang EK007 til terminal 4.";
            let mut fil = log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", linje);
        }
    })
}

// ----------------------------------------------------------------
// SIMULERINGS-MOTOR
// ----------------------------------------------------------------

/// Holder alle simulationens dele samlet.
/// Deles via Arc så tråde kan tilgå den.
struct Simulation {
    server: Arc<CentralServer>,
    // Skranker gemmes i en Arc<RwLock<...>> så vi kan tilføje nye skranker
    // dynamisk under kørslen - det er pointen med den dynamiske skalering!
    skranker: Arc<RwLock<Vec<Arc<Skranke>>>>,
    terminaler: Vec<Arc<Terminal>>,
    sorteringsanlæg: Arc<Sorteringsanlæg>,
    sortering_ind_buffer: Arc<(Mutex<Vec<Bagage>>, Condvar)>,
    tråd_handles: Mutex<Vec<thread::JoinHandle<()>>>,
    global_stop: Arc<AtomicBool>,
}

impl Simulation {
    fn ny(log_sti: &str) -> Self {
        // Opret central server med log-fil
        let mut server = CentralServer::ny(log_sti);
        server.indlæs_reservationer_fra_fil("reservationer.csv");
        server.opret_standard_flyveplan();

        // Den delte sorteringsbuffer - producer/consumer via Condvar
        let sortering_ind = Arc::new((Mutex::new(Vec::new()), Condvar::new()));
        let global_stop = Arc::new(AtomicBool::new(false));

        let server_arc = Arc::new(server);

        // Opret sorteringsanlæg
        let sortering = Arc::new(Sorteringsanlæg::ny(
            sortering_ind.clone(),
            server_arc.flyveplan.clone(),
            server_arc.hændelses_log.clone(),
            server_arc.log_fil.clone(),
            server_arc.statistik.clone(),
        ));

        // Opret terminaler baseret på flyveplan
        let terminaler: Vec<Arc<Terminal>> = {
            let plan = server_arc.flyveplan.read().unwrap();
            plan.iter()
                .map(|f| {
                    Arc::new(Terminal::ny(
                        f.terminal_nr,
                        &f.flight_nr,
                        server_arc.hændelses_log.clone(),
                        server_arc.log_fil.clone(),
                        server_arc.statistik.clone(),
                    ))
                })
                .collect()
        };

        // Registrér alle terminaler i sorteringsanlægget
        for terminal in &terminaler {
            sortering.registrér_terminal(terminal.id, terminal.buffer.clone());
        }

        Simulation {
            server: server_arc,
            skranker: Arc::new(RwLock::new(Vec::new())),
            terminaler,
            sorteringsanlæg: sortering,
            sortering_ind_buffer: sortering_ind,
            tråd_handles: Mutex::new(Vec::new()),
            global_stop,
        }
    }

    /// Åbner en ny skranke og starter dens tråd.
    /// Dette er den dynamiske skalering - vi kan kalde denne
    /// funktion under simulationen for at håndtere mere flow!
    fn åbn_skranke(&self, id: u32) {
        let skranke = Arc::new(Skranke::ny(
            id,
            self.sortering_ind_buffer.clone(),
            self.server.hændelses_log.clone(),
            self.server.log_fil.clone(),
            self.server.statistik.clone(),
        ));
        skranke.åbn();

        let mut skranker = self.skranker.write().unwrap();
        if skranker.iter().any(|s| s.id == id) {
            let linje = format!("[System] Skranke {} eksisterer allerede!", id);
            let mut log = self.server.hændelses_log.lock().unwrap();
            log.push(linje.clone());
            let mut fil = self.server.log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", linje);
            return;
        }
        skranker.push(skranke);
        let linje = format!("[System] Skranke {} tilføjet og åbnet.", id);
        {
            let mut log = self.server.hændelses_log.lock().unwrap();
            log.push(linje.clone());
            let mut fil = self.server.log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", linje);
        }
    }

    /// Lukker en specifik skranke
    fn luk_skranke(&self, id: u32) {
        let skranker = self.skranker.read().unwrap();
        if let Some(skranke) = skranker.iter().find(|s| s.id == id) {
            skranke.luk();
        } else {
            let linje = format!("[System] Skranke {} ikke fundet.", id);
            let mut log = self.server.hændelses_log.lock().unwrap();
            log.push(linje);
        }
    }

    /// Åbner alle terminaler og starter deres tråde
    fn start_terminaler(&self) {
        let mut handles = self.tråd_handles.lock().unwrap();
        for terminal in &self.terminaler {
            terminal.åbn();
            let handle = Terminal::start_terminal_tråd(
                terminal.id,
                terminal.flight_nr.clone(),
                terminal.is_åben.clone(),
                terminal.buffer.clone(),
                terminal.loadet_bagage.clone(),
                self.server.hændelses_log.clone(),
                self.server.log_fil.clone(),
                self.server.statistik.clone(),
                terminal.stop_signal.clone(),
            );
            handles.push(handle);
        }
    }

    /// Starter sorteringstråden
    fn start_sortering(&self) {
        let mut handles = self.tråd_handles.lock().unwrap();
        let handle = Sorteringsanlæg::start_sortering_tråd(
            self.sorteringsanlæg.ind_buffer.clone(),
            self.sorteringsanlæg.terminal_buffere.clone(),
            self.sorteringsanlæg.flyveplan.clone(),
            self.server.hændelses_log.clone(),
            self.server.log_fil.clone(),
            self.server.statistik.clone(),
            self.sorteringsanlæg.stop_signal.clone(),
        );
        handles.push(handle);
    }

    /// Starter flyveplan-opdateringstråden
    fn start_flyveplan_tråd(&self) {
        let mut handles = self.tråd_handles.lock().unwrap();
        let handle = start_flyveplan_opdaterings_tråd(
            self.server.flyveplan.clone(),
            self.server.log_fil.clone(),
            self.global_stop.clone(),
        );
        handles.push(handle);
    }

    /// Sender bagage fra alle åbne skranker til sortering.
    /// Kører i en separat tråd så det ikke blokerer UI.
    fn kør_skranke_tråde(&self, bagage_liste: Vec<(u32, Bagage)>) {
        // bagage_liste: (skranke_id, bagage)
        // Grupper bagage per skranke
        let mut per_skranke: HashMap<u32, Vec<Bagage>> = HashMap::new();
        for (sid, bag) in bagage_liste {
            per_skranke.entry(sid).or_default().push(bag);
        }

        let skranker_arc = self.skranker.clone();
        let mut handles = self.tråd_handles.lock().unwrap();

        for (skranke_id, bagager) in per_skranke {
            // Find skranken - clone Arc for tråden
            let skranke_opt = {
                let skranker = skranker_arc.read().unwrap();
                skranker.iter().find(|s| s.id == skranke_id).cloned()
            };

            if let Some(skranke) = skranke_opt {
                let handle = thread::spawn(move || {
                    // Hver skranke-tråd har sin egen RNG - forskelligt flow per skranke!
                    let rng = ny_rng();
                    for bagage in bagager {
                        // Passagerer ankommer ikke alle på én gang - realistisk ankomst-spredning
                        // 50-250ms mellem passagerer (folk stiller sig i kø over tid)
                        let ankomst_pause = rng.varighed_ms(50, 250);
                        thread::sleep(ankomst_pause);
                        skranke.modtag_bagage(bagage, &rng);
                    }
                    // Send alt bufferet bagage til sortering
                    skranke.send_til_sortering();
                });
                handles.push(handle);
            } else {
                let linje = format!("[System] Ingen åben skranke med ID {}.", skranke_id);
                let mut log = self.server.hændelses_log.lock().unwrap();
                log.push(linje);
            }
        }
    }

    /// Stopper alle tråde pænt
    fn stop_alle(&self) {
        self.global_stop.store(true, Ordering::SeqCst);
        self.sorteringsanlæg.stop_signal.store(true, Ordering::SeqCst);

        // Stop alle terminaler
        for terminal in &self.terminaler {
            terminal.stop_signal.store(true, Ordering::SeqCst);
            // Wake up condvars der måske sover
            let (_, cv) = &*terminal.buffer;
            cv.notify_all();
        }

        // Wake op sorteringsbufferen
        let (_, cv) = &*self.sortering_ind_buffer;
        cv.notify_all();
    }

    /// Venter på at alle tråde afslutter
    fn vent_på_alle(&self) {
        let mut handles = self.tråd_handles.lock().unwrap();
        while let Some(h) = handles.pop() {
            let _ = h.join();
        }
    }

    /// Udskriver statistik-rapport
    fn udskriv_rapport(&self) {
        let statistik = &self.server.statistik;
        let throughput = statistik.throughput();
        let gns_ventetid = statistik.gns_ventetid_ms();
        let total_behandlet = statistik.bagage_behandlet_total.load(Ordering::Relaxed);
        let sorteret = statistik.sortering_behandlet.load(Ordering::Relaxed);
        let loadet = statistik.terminaler_modtaget.load(Ordering::Relaxed);

        let rapport = format!(
            "\n\
            ╔══════════════════════════════════════════╗\n\
            ║       BAGAGESORTERING STATISTIK          ║\n\
            ╠══════════════════════════════════════════╣\n\
            ║  Throughput:       {:.2} bagage/sek        \n\
            ║  Gns. ventetid:    {:.1} ms/bagage          \n\
            ║  Total behandlet:  {} stk                  \n\
            ║  Sorteret:         {} stk                  \n\
            ║  Loadet på fly:    {} stk                  \n\
            ╚══════════════════════════════════════════╝",
            throughput, gns_ventetid, total_behandlet, sorteret, loadet
        );

        {
            let mut fil = self.server.log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", rapport);
        }

        for terminal in &self.terminaler {
            let loaded = terminal.loadet_bagage.lock().unwrap();
            let linje = format!(
                "[Terminal {}|{}] Loadet {} stk bagage: {:?}",
                terminal.id,
                terminal.flight_nr,
                loaded.len(),
                *loaded
            );
            let mut fil = self.server.log_fil.lock().unwrap();
            let _ = writeln!(fil, "{}", linje);
        }
    }
}

// ----------------------------------------------------------------
// RATATUI TUI APP
// ----------------------------------------------------------------

/// Input mode for TUI
#[derive(Debug, Clone, PartialEq)]
enum InputMode {
    Normal,
    ÅbnSkranke,
    LukSkranke,
}

/// TUI Application state
struct App {
    simulation: Arc<Simulation>,
    bagage_tæller: Arc<AtomicU64>,
    input_mode: InputMode,
    input_buffer: String,
    scroll_offset: u16,
    should_quit: bool,
}

impl App {
    fn ny(simulation: Arc<Simulation>) -> Self {
        App {
            simulation,
            bagage_tæller: Arc::new(AtomicU64::new(1)),
            input_mode: InputMode::Normal,
            input_buffer: String::new(),
            scroll_offset: 0,
            should_quit: false,
        }
    }

    fn handle_input(&mut self, key: KeyCode) {
        match self.input_mode {
            InputMode::Normal => {
                match key {
                    KeyCode::Char('q') | KeyCode::Esc => {
                        self.should_quit = true;
                    }
                    KeyCode::Char('o') => {
                        self.input_mode = InputMode::ÅbnSkranke;
                        self.input_buffer.clear();
                    }
                    KeyCode::Char('c') => {
                        self.input_mode = InputMode::LukSkranke;
                        self.input_buffer.clear();
                    }
                    KeyCode::Char('r') => {
                        self.kør_simulering();
                    }
                    KeyCode::Up => {
                        self.scroll_offset = self.scroll_offset.saturating_sub(1);
                    }
                    KeyCode::Down => {
                        self.scroll_offset = self.scroll_offset.saturating_add(1);
                    }
                    _ => {}
                }
            }
            InputMode::ÅbnSkranke | InputMode::LukSkranke => {
                match key {
                    KeyCode::Enter => {
                        if let Ok(id) = self.input_buffer.parse::<u32>() {
                            if self.input_mode == InputMode::ÅbnSkranke {
                                self.simulation.åbn_skranke(id);
                            } else {
                                self.simulation.luk_skranke(id);
                            }
                        }
                        self.input_mode = InputMode::Normal;
                        self.input_buffer.clear();
                    }
                    KeyCode::Esc => {
                        self.input_mode = InputMode::Normal;
                        self.input_buffer.clear();
                    }
                    KeyCode::Char(c) => {
                        self.input_buffer.push(c);
                    }
                    KeyCode::Backspace => {
                        self.input_buffer.pop();
                    }
                    _ => {}
                }
            }
        }
    }

    fn kør_simulering(&self) {
        let åbne_skranke_ids: Vec<u32> = {
            let skranker = self.simulation.skranker.read().unwrap();
            skranker
                .iter()
                .filter(|s| s.is_åben.load(Ordering::SeqCst))
                .map(|s| s.id)
                .collect()
        };

        if åbne_skranke_ids.is_empty() {
            return;
        }

        let reservationer = self.simulation.server.reservationer.clone();
        let mut bagage_assignments: Vec<(u32, Bagage)> = Vec::new();

        for (idx, reservation) in reservationer.iter().enumerate() {
            let skranke_id = åbne_skranke_ids[idx % åbne_skranke_ids.len()];
            let bag_nr = self.bagage_tæller.fetch_add(1, Ordering::Relaxed);
            let bagage = Bagage::ny(
                &format!("BAG{:04}", bag_nr),
                reservation.passager_nr,
                &reservation.flyafgang,
                skranke_id,
            );
            bagage_assignments.push((skranke_id, bagage));
        }

        self.simulation.kør_skranke_tråde(bagage_assignments);
    }
}

/// Render TUI
fn ui(f: &mut Frame, app: &App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(3),
            Constraint::Min(10),
            Constraint::Length(3),
        ])
        .split(f.size());

    let title = Paragraph::new("LUFTHAVN BAGAGESORTERINGSSYSTEM")
        .style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD))
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(title, chunks[0]);

    let main_chunks = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([Constraint::Percentage(50), Constraint::Percentage(50)])
        .split(chunks[1]);

    let left_chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Percentage(40), Constraint::Percentage(60)])
        .split(main_chunks[0]);

    render_status(f, app, left_chunks[0]);
    render_flyveplan(f, app, left_chunks[1]);

    let right_chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Percentage(30), Constraint::Percentage(70)])
        .split(main_chunks[1]);

    render_statistik(f, app, right_chunks[0]);
    render_log(f, app, right_chunks[1]);

    render_footer(f, app, chunks[2]);
}

fn render_status(f: &mut Frame, app: &App, area: Rect) {
    let mut items = Vec::new();

    items.push(ListItem::new(Line::from(vec![
        Span::styled("SKRANKER:", Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
    ])));

    let skranker = app.simulation.skranker.read().unwrap();
    if skranker.is_empty() {
        items.push(ListItem::new("  Ingen skranker åbnet"));
    } else {
        for s in skranker.iter() {
            let status = if s.is_åben.load(Ordering::SeqCst) { "ÅBEN" } else { "LUKKET" };
            let buf_len = s.udgående_buffer.lock().unwrap().len();
            let color = if s.is_åben.load(Ordering::SeqCst) { Color::Green } else { Color::Red };
            items.push(ListItem::new(Line::from(vec![
                Span::raw("  Skranke "),
                Span::styled(format!("{}", s.id), Style::default().fg(color).add_modifier(Modifier::BOLD)),
                Span::raw(format!(" [{}] Buffer: {}/{}", status, buf_len, SKRANKE_BUFFER_KAPACITET)),
            ])));
        }
    }

    items.push(ListItem::new(""));
    items.push(ListItem::new(Line::from(vec![
        Span::styled("TERMINALER:", Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
    ])));

    for t in &app.simulation.terminaler {
        let status = if t.is_åben.load(Ordering::SeqCst) { "ÅBEN" } else { "LUKKET" };
        let (buf_lås, _) = &*t.buffer;
        let buf_len = buf_lås.lock().unwrap().len();
        let loadet = t.loadet_bagage.lock().unwrap().len();
        let color = if t.is_åben.load(Ordering::SeqCst) { Color::Green } else { Color::Red };
        items.push(ListItem::new(Line::from(vec![
            Span::raw("  Terminal "),
            Span::styled(format!("{}", t.id), Style::default().fg(color).add_modifier(Modifier::BOLD)),
            Span::raw(format!(" [{}] {} | Buf: {}/{} | Loadet: {}",
                status, t.flight_nr, buf_len, TERMINAL_BUFFER_KAPACITET, loadet)),
        ])));
    }

    items.push(ListItem::new(""));
    let (sort_lås, _) = &*app.simulation.sortering_ind_buffer;
    let sort_len = sort_lås.lock().unwrap().len();
    let sort_pct = (sort_len as f64 / SORTERING_BUFFER_KAPACITET as f64 * 100.0) as u16;
    items.push(ListItem::new(Line::from(vec![
        Span::styled("SORTERING: ", Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
        Span::raw(format!("{}/{} ({}%)", sort_len, SORTERING_BUFFER_KAPACITET, sort_pct)),
    ])));

    let list = List::new(items)
        .block(Block::default().borders(Borders::ALL).title("Status"));
    f.render_widget(list, area);
}

fn render_flyveplan(f: &mut Frame, app: &App, area: Rect) {
    let plan = app.simulation.server.flyveplan.read().unwrap();
    let items: Vec<ListItem> = plan
        .iter()
        .map(|fly| {
            let status_color = if fly.aktiv { Color::Green } else { Color::Gray };
            let status_text = if fly.aktiv { "AKTIV" } else { "INAKTIV" };
            ListItem::new(Line::from(vec![
                Span::styled(&fly.flight_nr, Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD)),
                Span::raw(" → Terminal "),
                Span::styled(format!("{}", fly.terminal_nr), Style::default().fg(Color::Yellow)),
                Span::raw(format!(" | {}", fly.afgang_tid)),
                Span::raw(" ["),
                Span::styled(status_text, Style::default().fg(status_color)),
                Span::raw("]"),
            ]))
        })
        .collect();

    let list = List::new(items)
        .block(Block::default().borders(Borders::ALL).title("Flyveplan"));
    f.render_widget(list, area);
}

fn render_statistik(f: &mut Frame, app: &App, area: Rect) {
    let statistik = &app.simulation.server.statistik;
    let throughput = statistik.throughput();
    let gns_ventetid = statistik.gns_ventetid_ms();
    let total_behandlet = statistik.bagage_behandlet_total.load(Ordering::Relaxed);
    let sorteret = statistik.sortering_behandlet.load(Ordering::Relaxed);
    let loadet = statistik.terminaler_modtaget.load(Ordering::Relaxed);

    let text = vec![
        Line::from(vec![
            Span::styled("Throughput: ", Style::default().fg(Color::Yellow)),
            Span::styled(format!("{:.2} bagage/sek", throughput), Style::default().fg(Color::Green).add_modifier(Modifier::BOLD)),
        ]),
        Line::from(vec![
            Span::styled("Gns. ventetid: ", Style::default().fg(Color::Yellow)),
            Span::raw(format!("{:.1} ms", gns_ventetid)),
        ]),
        Line::from(""),
        Line::from(vec![
            Span::styled("Total behandlet: ", Style::default().fg(Color::Cyan)),
            Span::raw(format!("{} stk", total_behandlet)),
        ]),
        Line::from(vec![
            Span::styled("Sorteret: ", Style::default().fg(Color::Cyan)),
            Span::raw(format!("{} stk", sorteret)),
        ]),
        Line::from(vec![
            Span::styled("Loadet på fly: ", Style::default().fg(Color::Cyan)),
            Span::raw(format!("{} stk", loadet)),
        ]),
    ];

    let paragraph = Paragraph::new(text)
        .block(Block::default().borders(Borders::ALL).title("Statistik"))
        .wrap(Wrap { trim: true });
    f.render_widget(paragraph, area);
}

fn render_log(f: &mut Frame, app: &App, area: Rect) {
    let log = app.simulation.server.hændelses_log.lock().unwrap();
    let total_lines = log.len();
    let visible_lines = area.height.saturating_sub(2) as usize;
    let start_idx = if app.scroll_offset == 0 && total_lines > visible_lines {
        total_lines.saturating_sub(visible_lines)
    } else if total_lines > visible_lines {
        total_lines.saturating_sub(visible_lines).saturating_sub(app.scroll_offset as usize)
    } else {
        0
    };

    let items: Vec<ListItem> = log
        .iter()
        .skip(start_idx)
        .take(visible_lines)
        .map(|line| {
            let style = if line.contains("✓") || line.contains("ÅBNET") {
                Style::default().fg(Color::Green)
            } else if line.contains("⚠") || line.contains("KØ") {
                Style::default().fg(Color::Yellow)
            } else if line.contains("ADVARSEL") || line.contains("LUKKET") {
                Style::default().fg(Color::Red)
            } else if line.contains("✈") {
                Style::default().fg(Color::Cyan)
            } else {
                Style::default()
            };
            ListItem::new(line.as_str()).style(style)
        })
        .collect();

    let list = List::new(items)
        .block(Block::default().borders(Borders::ALL).title(format!("Hændelseslog ({} linjer)", total_lines)));
    f.render_widget(list, area);
}

fn render_footer(f: &mut Frame, app: &App, area: Rect) {
    let text = match app.input_mode {
        InputMode::Normal => {
            Line::from(vec![
                Span::styled("[O]", Style::default().fg(Color::Green).add_modifier(Modifier::BOLD)),
                Span::raw(" Åbn skranke | "),
                Span::styled("[C]", Style::default().fg(Color::Red).add_modifier(Modifier::BOLD)),
                Span::raw(" Luk skranke | "),
                Span::styled("[R]", Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD)),
                Span::raw(" Kør simulering | "),
                Span::styled("[↑↓]", Style::default().fg(Color::Yellow)),
                Span::raw(" Scroll log | "),
                Span::styled("[Q/ESC]", Style::default().fg(Color::Magenta).add_modifier(Modifier::BOLD)),
                Span::raw(" Afslut"),
            ])
        }
        InputMode::ÅbnSkranke => {
            Line::from(vec![
                Span::styled("Åbn skranke - Indtast ID: ", Style::default().fg(Color::Green)),
                Span::styled(&app.input_buffer, Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
                Span::raw(" [Enter: OK | ESC: Annuller]"),
            ])
        }
        InputMode::LukSkranke => {
            Line::from(vec![
                Span::styled("Luk skranke - Indtast ID: ", Style::default().fg(Color::Red)),
                Span::styled(&app.input_buffer, Style::default().fg(Color::White).add_modifier(Modifier::BOLD)),
                Span::raw(" [Enter: OK | ESC: Annuller]"),
            ])
        }
    };

    let paragraph = Paragraph::new(text)
        .block(Block::default().borders(Borders::ALL));
    f.render_widget(paragraph, area);
}

// ----------------------------------------------------------------
// MAIN
// ----------------------------------------------------------------

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let sim = Arc::new(Simulation::ny("system_log.txt"));

    sim.start_sortering();
    sim.start_terminaler();
    sim.start_flyveplan_tråd();
    sim.server.statistik.start();

    enable_raw_mode()?;
    let mut stdout = std::io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = RatatuiTerminal::new(backend)?;
    terminal.hide_cursor()?;

    let mut app = App::ny(sim.clone());

    let tick_rate = Duration::from_millis(50);
    let mut last_tick = Instant::now();

    loop {
        terminal.draw(|f| ui(f, &app))?;

        let timeout = tick_rate.saturating_sub(last_tick.elapsed());
        if event::poll(timeout)? {
            if let Event::Key(key) = event::read()? {
                if key.kind == KeyEventKind::Press {
                    app.handle_input(key.code);
                }
            }
        }

        if last_tick.elapsed() >= tick_rate {
            last_tick = Instant::now();
        }

        if app.should_quit {
            break;
        }
    }

    terminal.clear()?;
    terminal.show_cursor()?;
    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;

    thread::sleep(Duration::from_millis(800));
    sim.stop_alle();
    sim.vent_på_alle();

    println!("\n[System] Alle tråde stoppet. Endelig rapport:");
    sim.udskriv_rapport();
    println!("\nFarvel! Log gemt i system_log.txt");

    Ok(())
}
