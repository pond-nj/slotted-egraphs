# RUST_BACKTRACE=full cargo test chc::leafDrop::mainTest -- --nocapture &> tmp2.txt
# RUST_BACKTRACE=1 cargo test chc::pairingPaperArray::mainTest -- --nocapture &> tmp2.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::leafDrop::testSortAppId -- --nocapture &> tmp2.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test arith::const_prop::const_prop -- --nocapture &> tmp.txt
 
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test tmptest -- --nocapture &> tmp2 

#  RUST_LOG=DEBUG RUST_BACKTRACE=1 heaptrack ./target/debug/deps/entry-36fa62a2ee92b610 chc::leafDrop::testSortAppId --nocapture &> tmp2.txt  
# target/debug/deps/entry-78c4a838346e1ec6
# RUST_LOG=DEBUG RUST_BACKTRACE=1 heaptrack ./target/debug/deps/entry-78c4a838346e1ec6 chc::leafDrop::mainTest --nocapture &> tmp2.txt  


# flamegraph -- target/debug/deps/entry-082ab240f6b1cb3f --nocapture chc::pairingPaperArray::mainTest
# flamegraph -- target/debug/deps/entry-0f36484c7ec5a013 --nocapture chc::leafDrop::mainTest


RUST_BACKTRACE=1 cargo test arith::tst::t5 &> tmp2.txt