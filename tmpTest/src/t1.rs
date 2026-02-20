use nauty_Traces_sys::*;
use std::os::raw::c_int;
use std::slice;

extern "C" fn writeautom(p: *mut i32, n: i32) {
    for i in 0..n {
        print!(" {:2}", unsafe { *p.offset(i as isize) })
    }
    println!()
}

fn nautyex3() {
    // nautyex3.c nauty example

    let mut options = optionblk::default();
    let mut stats = statsblk::default();

    /* The following cause nauty to call two procedures which
    store the group information as nauty runs. */

    options.userautomproc = Some(groupautomproc);
    options.userlevelproc = Some(grouplevelproc);

    for n in 1..20 {
        let m = SETWORDSNEEDED(n);
        unsafe {
            nauty_check(
                WORDSIZE as c_int,
                m as c_int,
                n as c_int,
                NAUTYVERSIONID as c_int,
            );
        }

        let mut g = empty_graph(n, m);
        let mut lab = vec![0; n];
        let mut ptn = vec![0; n];
        let mut orbits = vec![0; n];

        for v in 0..n {
            ADDONEEDGE(&mut g, v, (v + 1) % n, m)
        }

        println!("Automorphisms of C[{}]:", n);

        unsafe {
            densenauty(
                g.as_mut_ptr(),
                lab.as_mut_ptr(),
                ptn.as_mut_ptr(),
                orbits.as_mut_ptr(),
                &mut options,
                &mut stats,
                m as c_int,
                n as c_int,
                std::ptr::null_mut(),
            );

            /* Get a pointer to the structure in which the group information
            has been stored.  If you use TRUE as an argument, the
            structure will be "cut loose" so that it won't be used
            again the next time nauty() is called.  Otherwise, as
            here, the same structure is used repeatedly. */

            let group = groupptr(FALSE);

            /* Expand the group structure to include a full set of coset
            representatives at every level.  This step is necessary
            if allgroup() is to be called. */

            makecosetreps(group);

            /* Call the procedure writeautom() for every element of the group.
            The first call is always for the identity. */

            allgroup(group, Some(writeautom));
        }
    }
}
