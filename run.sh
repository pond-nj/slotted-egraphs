# RUST_BACKTRACE=1 cargo test chc::leafDrop::mainTest -- --nocapture &> tmp.txt
RUST_BACKTRACE=full cargo test chc::leafDrop2::mainTest -- --nocapture &> tmp.txt
# RUST_BACKTRACE=1 cargo test chc::pairingPaperArray::mainTest -- --nocapture &> tmp.txt
# RUST_BACKTRACE=1 cargo test --release arith2::tst::t7 -- --nocapture &> tmp.txt
# cargo test --release --test entry chc::leafDrop2::mainTest --features log,adtDefine -- --test-threads=1 --nocapture &> tmp.txt
# cargo test --release --test entry chc::pairingPaperArray::mainTest --features log,adtDefine,pairingDefine -- --test-threads=1 --nocapture &> tmp.txt
# RUST_BACKTRACE=1 cargo test chc::synchronizedCHC::mainTest -- --nocapture &> tmp.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::leafDrop::testSortAppId -- --nocapture &> tmp.txt
 
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test tmptest -- --nocapture &> tmp2 

#  RUST_LOG=DEBUG RUST_BACKTRACE=1 heaptrack ./target/debug/deps/entry-36fa62a2ee92b610 chc::leafDrop::testSortAppId --nocapture &> tmp.txt  
# target/debug/deps/entry-78c4a838346e1ec6
# RUST_LOG=DEBUG RUST_BACKTRACE=1 heaptrack ./target/debug/deps/entry-78c4a838346e1ec6 chc::leafDrop::mainTest --nocapture &> tmp.txt  


# flamegraph -o pairingPaperArray.svg -- target/debug/deps/entry-f45f2bd9100da93c --nocapture chc::pairingPaperArray::mainTest
# flamegraph -o leafDrop.svg -- target/debug/deps/entry-aafa1e403367dd3e --nocapture chc::leafDrop::mainTest
# flamegraph -o leafDrop2.svg -- target/debug/deps/entry-2e8397d70bde19e9 --nocapture chc::leafDrop2::mainTest

# flamegraph -o arith2.svg -- target/debug/deps/entry-cbca4b0766c10a4e --nocapture arith2::tst::t7


# flamegraph -o arith2.svg -- target/debug/deps/entry-6ea56ee94ebe381b --nocapture arith2::tst::t7


# RUST_BACKTRACE=1 cargo test arith::tst::t2   &> tmp.txt

# rust-gdb target/debug/deps/entry-38a92d690cfd6aa3
# set args --test entry --nocapture lambda::native::y_identity
# run

# replace min-leaf => minLeaf
# regex -(\w) => \U$1
