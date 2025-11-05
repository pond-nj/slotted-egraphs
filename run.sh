# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc -- --nocapture &> tmp
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test arith -- --nocapture &> tmp
RUST_LOG=debug RUST_BACKTRACE=1 cargo test lambda::lambda_small_step::add_y_step -- --nocapture &> tmp