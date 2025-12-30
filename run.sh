# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc -- --nocapture &> tmp.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::leafDrop::minLeafAndMinTest -- --nocapture &> tmp.txt
RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::leafDrop::mainTest -- --nocapture &> tmp2.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::leafDrop::testSortAppId -- --nocapture &> tmp2.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test arith::const_prop::const_prop -- --nocapture &> tmp.txt
 
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test tmptest -- --nocapture &> tmp2 

#  RUST_LOG=DEBUG RUST_BACKTRACE=1 heaptrack ./target/debug/deps/entry-78c4a838346e1ec6 chc::leafDrop::testSortAppId --nocapture &> tmp2.txt  
# target/debug/deps/entry-78c4a838346e1ec6
# RUST_LOG=DEBUG RUST_BACKTRACE=1 heaptrack ./target/debug/deps/entry-78c4a838346e1ec6 chc::leafDrop::mainTest --nocapture &> tmp2.txt  