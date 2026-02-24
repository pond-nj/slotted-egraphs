RUST_BACKTRACE=1 cargo test chc::leafDrop::mainTest -- --nocapture &> tmp.txt
# RUST_BACKTRACE=1 cargo test chc::pairingPaperArray::mainTest -- --nocapture &> tmp.txt
# RUST_BACKTRACE=1 cargo test chc::synchronizedCHC::mainTest -- --nocapture &> tmp.txt
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test chc::leafDrop::testSortAppId -- --nocapture &> tmp.txt
 
# RUST_LOG=debug RUST_BACKTRACE=1 cargo test tmptest -- --nocapture &> tmp2 

#  RUST_LOG=DEBUG RUST_BACKTRACE=1 heaptrack ./target/debug/deps/entry-36fa62a2ee92b610 chc::leafDrop::testSortAppId --nocapture &> tmp.txt  
# target/debug/deps/entry-78c4a838346e1ec6
# RUST_LOG=DEBUG RUST_BACKTRACE=1 heaptrack ./target/debug/deps/entry-78c4a838346e1ec6 chc::leafDrop::mainTest --nocapture &> tmp.txt  


# flamegraph -o pairingPaperArray.svg -- target/debug/deps/entry-38a92d690cfd6aa3 --nocapture chc::pairingPaperArray::mainTest
# flamegraph -o leafDrop2.svg -- target/debug/deps/entry-9180f215c26aedec --nocapture chc::leafDrop::mainTest


# RUST_BACKTRACE=1 cargo test lambda::native::y_identity &> tmp.txt

# rust-gdb target/debug/deps/entry-38a92d690cfd6aa3
# set args --test entry --nocapture lambda::native::y_identity
# run
