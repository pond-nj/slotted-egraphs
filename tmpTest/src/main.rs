use log::{Level, LevelFilter, Log, Metadata, Record};
use std::panic;
use std::sync::{Mutex, Once};

struct RingLogger {
    buf: Mutex<Vec<String>>,
    cap: usize,
}

impl RingLogger {
    const fn new(cap: usize) -> Self {
        Self {
            buf: Mutex::new(Vec::new()),
            cap,
        }
    }

    fn dump_to_stderr(&self) {
        eprintln!("=== last {} log entries ===", self.cap);
        let buf = self.buf.lock().unwrap();
        for line in buf.iter() {
            eprintln!("{line}");
        }
    }
}

impl Log for RingLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Info
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let mut buf = self.buf.lock().unwrap();
        if buf.len() == self.cap {
            // drop oldest
            buf.remove(0);
        }
        buf.push(format!("{} - {}", record.level(), record.args()));
    }

    fn flush(&self) {}
}

// Safe because all interior mutability is behind a Mutex.
static LOGGER: RingLogger = RingLogger::new(100);
static INIT: Once = Once::new();

fn init_logging() {
    INIT.call_once(|| {
        log::set_logger(&LOGGER).unwrap();
        log::set_max_level(LevelFilter::Info);

        panic::set_hook(Box::new(|info| {
            // This log entry itself goes into the ring buffer.
            log::error!("panic: {info}");
            // Then we dump the last N entries.
            LOGGER.dump_to_stderr();
        }));
    });
}

fn main() {
    init_logging();

    log::info!("starting up");
    log::info!("doing some work");
    // ...
    panic!("boom");
}
