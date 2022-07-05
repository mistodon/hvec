#[test]
#[cfg(not(feature = "no_drop"))]
pub fn push_and_drop_runs_destructors() {
    use hvec::HVec;

    static mut A_COUNT: u8 = 0;
    static mut B_COUNT: u8 = 0;

    struct A(u8);
    struct B(u8);

    impl A {
        pub fn new() -> Self {
            unsafe {
                let x = A_COUNT;
                A_COUNT += 1;
                A(x)
            }
        }
    }
    impl Drop for A {
        fn drop(&mut self) {
            unsafe {
                A_COUNT -= 1;
            }
        }
    }

    impl B {
        pub fn new() -> Self {
            unsafe {
                let x = B_COUNT;
                B_COUNT += 1;
                B(x)
            }
        }
    }
    impl Drop for B {
        fn drop(&mut self) {
            unsafe {
                B_COUNT -= 1;
            }
        }
    }

    {
        let a0 = A::new();
        let a1 = A::new();
        let b0 = B::new();
        let b1 = B::new();
        let b2 = B::new();
        let s = String::from("Hello");

        let mut hvec = HVec::new();
        hvec.push(a0);
        hvec.push(b0);
        hvec.push(a1);
        hvec.push(b1);
        hvec.push(s);
        hvec.push(b2);
    }

    unsafe {
        assert_eq!(A_COUNT, 0);
        assert_eq!(B_COUNT, 0);
    }
}
