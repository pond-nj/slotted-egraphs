# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc -- --nocapture &> tmp
RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::tst::tst1 -- --nocapture &> tmp
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test arith::const_prop::const_prop -- --nocapture &> tmp