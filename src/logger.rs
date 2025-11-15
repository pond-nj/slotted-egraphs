use std::sync::Once;

use env_logger::Builder;
use log::{debug, LevelFilter};

static INIT_LOGGER: Once = Once::new();

pub fn initLogger() {
    INIT_LOGGER.call_once(|| {
        // This closure runs exactly once, globally.
        // env_logger::builder()
        //     .format_timestamp(None)
        //     .format_level(false)
        //     .format_target(true)
        //     .filter_level(LevelFilter::Debug)
        //     .init();
    });
}
