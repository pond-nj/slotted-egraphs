# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc -- --nocapture &> tmp.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::leafDrop::minLeafAndMinTest -- --nocapture &> tmp.txt
RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::leafDrop::mainTest -- --nocapture &> tmp2.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test arith::const_prop::const_prop -- --nocapture &> tmp.txt
 
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test tmptest -- --nocapture &> tmp2