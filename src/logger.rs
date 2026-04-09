use std::sync::Once;

use env_logger::Builder;
use log::{debug, LevelFilter};

static _INIT_LOGGER: Once = Once::new();
const LOG: bool = true;

pub fn initLogger() {
    if LOG {
        _INIT_LOGGER.call_once(|| {
            env_logger::builder()
                .format_timestamp(None)
                .format_level(true)
                .format_target(true)
                .filter_level(LevelFilter::Info)
                .init();
        });
    }
}
