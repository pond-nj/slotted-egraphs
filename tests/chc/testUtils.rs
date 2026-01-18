#[macro_export]
macro_rules! checkRes {
    ($keyword: expr, $res:expr) => {
        assert!(
            $res.len() > 0,
            "{} is empty, expected at least one element.",
            $keyword
        );

        let allIds = $res.iter().map(|x| &x.1).collect::<BTreeSet<_>>();

        assert!(
            allIds.len() == 1,
            "Expected all elements to have the same ID. Found IDs: {:?}",
            allIds
        );
    };
}
