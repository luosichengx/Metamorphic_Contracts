use std::collections::HashSet;

#[derive(Clone, Eq, PartialEq)]
pub struct Library {
    available: HashSet<String>,
    lent: HashSet<String>,
}

#[derive(Clone, Eq, PartialEq)]
pub struct Book {
    id: usize,
    author: String,
}

impl Book{
    pub fn add(mut self, modi:usize) -> Book{
        self.id = self.id + modi;
        self
    }

    pub fn reverse(mut self) -> Book{
        self.id = 100 - self.id;
        self
    }

    pub fn merge(mut self, modi:Book) -> Book{
        self.id = self.id + modi.id;
        self
    }

    pub fn ref_add(&mut self, modi:usize) -> &Book{
        (*self).id = self.id + modi;
        self
    }

    pub fn ref_reverse(&mut self) -> &Book{
        (*self).id = 100 - self.id;
        self
    }

    pub fn ref_merge(&mut self, modi:Book) -> &Book{
        (*self).id = self.id + modi.id;
        self
    }
}

impl Library {
    // #[ensures(self == old(self), "No change")]
    fn book_exists(&self, book_id: usize) -> bool {
        self.available.contains(&book_id.to_string()) || self.lent.contains(&book_id.to_string())
    }

    fn book_exist(&self, book_id:  &str) -> bool {
        self.available.contains(book_id) || self.lent.contains(book_id)
    }
    
    pub fn add_book(&mut self, book_id: usize) -> usize{
        let __contract_old_0 = self . available . len() ; let book_id_contract_2 =
        2 * 1 - book_id ; let book_id_contract_3 = 1 + book_id ; let
        book_id_contract_4 = 1 ; let book_id_contract_5 = book_id + 1 ; let
        book_id_contract_6 = book_id + 1 ; let mut self_contract_1 = self .
        clone() ; let mut self_contract_2 = self . clone() ; let mut
        self_contract_3 = self . clone() ; let mut self_contract_4 = self .
        clone() ; let mut self_contract_5 = self . clone() ; let mut
        self_contract_6 = self . clone() ; debug_assert !
        (! self . book_exists(book_id), concat !
         (concat !
          ("Pre-condition of add_book violated: Book IDs are unique", ": "),
          stringify ! (! self . book_exists(book_id)))) ; #[allow(unused_mut)] let
        mut run = || -> usize
        {
            self . available . insert((book_id + 1) . to_string()) ; self .
            available . len()
        } ; let ret = run() ; let book_id_contract_1 = ret . clone() ;
        debug_assert !
        (! self . book_exists(book_id_contract_1), concat !
         (concat !
          ("Pre-condition of add_book violated: Book IDs are unique", ": "),
          stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run1 = || -> usize
        {
            self_contract_1 . available .
            insert((book_id_contract_1 + 1) . to_string()) ; self_contract_1 .
            available . len()
        } ; let ret1 = run1() ; debug_assert !
        (! self . book_exists(book_id_contract_2), concat !
         (concat !
          ("Pre-condition of add_book violated: Book IDs are unique", ": "),
          stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run2 = || -> usize
        {
            self_contract_2 . available .
            insert((book_id_contract_2 + 1) . to_string()) ; self_contract_2 .
            available . len()
        } ; let ret2 = run2() ; debug_assert !
        (! self . book_exists(book_id_contract_3), concat !
         (concat !
          ("Pre-condition of add_book violated: Book IDs are unique", ": "),
          stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run3 = || -> usize
        {
            self_contract_3 . available .
            insert((book_id_contract_3 + 1) . to_string()) ; self_contract_3 .
            available . len()
        } ; let ret3 = run3() ; debug_assert !
        (! self . book_exists(book_id_contract_4), concat !
         (concat !
          ("Pre-condition of add_book violated: Book IDs are unique", ": "),
          stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run4 = || -> usize
        {
            self_contract_4 . available .
            insert((book_id_contract_4 + 1) . to_string()) ; self_contract_4 .
            available . len()
        } ; let ret4 = run4() ; debug_assert !
        (! self . book_exists(book_id_contract_5), concat !
         (concat !
          ("Pre-condition of add_book violated: Book IDs are unique", ": "),
          stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run5 = || -> usize
        {
            self_contract_5 . available .
            insert((book_id_contract_5 + 1) . to_string()) ; self_contract_5 .
            available . len()
        } ; let ret5 = run5() ; debug_assert !
        (! self . book_exists(book_id_contract_6), concat !
         (concat !
          ("Pre-condition of add_book violated: Book IDs are unique", ": "),
          stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run6 = || -> usize
        {
            self_contract_6 . available .
            insert((book_id_contract_6 + 1) . to_string()) ; self_contract_6 .
            available . len()
        } ; let ret6 = run6() ; #[cfg(test)]
        {
            debug_assert !
            (ret + ret == ret1 + book_id, concat !
             (concat !
              ("iter_consistency of add_book violated: my iter consistency test",
               ": "), stringify ! ("f(f(x)) - f(x) = f(x) - x"))) ;
        } #[cfg(test)]
        {
            debug_assert !
            (ret == - ret2, concat !
             (concat ! ("symmetry of add_book violated: my symmetry test", ": "),
              stringify ! ("f(x) = ±f(2*y - x)"))) ;
        } #[cfg(test)]
        {
            debug_assert !
            (ret < ret3, concat !
             (concat !
              ("monotonicity of add_book violated: my monotonicity test", ": "),
              stringify ! ("x < y -> f(x) < f(y)"))) ;
        } #[cfg(test)]
        {
            debug_assert !
            (ret == ret4 + ret5, concat !
             (concat !
              ("homomorphism of add_book violated: my homomorphism test", ": "),
              stringify ! ("f(x) + f(y) = f(x + y)"))) ;
        } #[cfg(test)]
        {
            debug_assert !
            (ret == ret6, concat !
             (concat !
              ("cyclicity of add_book violated: my cyclicity test", ": "),
              stringify ! ("f(x + t) = f(x)"))) ;
        } assert !
        (self . available . len() == __contract_old_0 + 1, concat !
         (concat ! ("Post-condition of add_book violated", ": "), stringify !
          (self . available . len() == old(self . available . len()) + 1))) ; ret
    }

    pub fn lend(&mut self, book_id: & str) -> & str
    {
        let book_id_contract_2 = format !
        ("{}{}", book_id . to_string(), "1" . to_string()) ; let
        book_id_contract_2 = book_id_contract_2 . as_str() ; let
        book_id_contract_3 = "1" ; let book_id_contract_4 = format !
        ("{}{}", book_id . to_string(), "1" . to_string()) ; let
        book_id_contract_4 = book_id_contract_4 . as_str() ; let
        book_id_contract_5 = format !
        ("{}{}", book_id . to_string(), "1" . to_string()) ; let
        book_id_contract_5 = book_id_contract_5 . as_str() ; let mut
        self_contract_1 = self . clone() ; let mut self_contract_2 = self .
        clone() ; let mut self_contract_3 = self . clone() ; let mut
        self_contract_4 = self . clone() ; let mut self_contract_5 = self .
        clone() ; debug_assert !
        (self . book_exist(book_id), concat !
         (concat ! ("Pre-condition of lend violated", ": "), stringify !
          (self . book_exist(book_id)))) ; #[allow(unused_mut)] let mut run = ||
        -> & str
        {
            if self . available . contains(book_id)
            {
                self . available . remove(book_id) ; self . lent .
                insert(book_id . to_string()) ; "a"
            } else { "b" }
        } ; let ret = run() ; let book_id_contract_1 = ret . clone() ;
        debug_assert !
        (self . book_exist(book_id_contract_1), concat !
         (concat ! ("Pre-condition of lend violated", ": "), stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run1 = || -> & str
        {
            if self_contract_1 . available . contains(book_id_contract_1)
            {
                self_contract_1 . available . remove(book_id_contract_1) ;
                self_contract_1 . lent . insert(book_id_contract_1 . to_string())
                ; "a"
            } else { "b" }
        } ; let ret1 = run1() ; debug_assert !
        (self . book_exist(book_id_contract_2), concat !
         (concat ! ("Pre-condition of lend violated", ": "), stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run2 = || -> & str
        {
            if self_contract_2 . available . contains(book_id_contract_2)
            {
                self_contract_2 . available . remove(book_id_contract_2) ;
                self_contract_2 . lent . insert(book_id_contract_2 . to_string())
                ; "a"
            } else { "b" }
        } ; let ret2 = run2() ; debug_assert !
        (self . book_exist(book_id_contract_3), concat !
         (concat ! ("Pre-condition of lend violated", ": "), stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run3 = || -> & str
        {
            if self_contract_3 . available . contains(book_id_contract_3)
            {
                self_contract_3 . available . remove(book_id_contract_3) ;
                self_contract_3 . lent . insert(book_id_contract_3 . to_string())
                ; "a"
            } else { "b" }
        } ; let ret3 = run3() ; debug_assert !
        (self . book_exist(book_id_contract_4), concat !
         (concat ! ("Pre-condition of lend violated", ": "), stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run4 = || -> & str
        {
            if self_contract_4 . available . contains(book_id_contract_4)
            {
                self_contract_4 . available . remove(book_id_contract_4) ;
                self_contract_4 . lent . insert(book_id_contract_4 . to_string())
                ; "a"
            } else { "b" }
        } ; let ret4 = run4() ; debug_assert !
        (self . book_exist(book_id_contract_5), concat !
         (concat ! ("Pre-condition of lend violated", ": "), stringify !
          ("extra run input against the pre-condition input assumption"))) ;
        #[allow(unused_mut)] let mut run5 = || -> & str
        {
            if self_contract_5 . available . contains(book_id_contract_5)
            {
                self_contract_5 . available . remove(book_id_contract_5) ;
                self_contract_5 . lent . insert(book_id_contract_5 . to_string())
                ; "a"
            } else { "b" }
        } ; let ret5 = run5() ; 
        {
            debug_assert !
            (format ! ("{}{}", ret . to_string(), ret . to_string()) . as_str() ==
             format ! ("{}{}", ret1 . to_string(), book_id . to_string()) .
             as_str(), concat !
             (concat !
              ("iter_consistency of lend violated: my iter consistency test",
               ": "), stringify ! ("f(f(x)) - f(x) = f(x) - x"))) ;
        } 
        {
            debug_assert !
            (ret < ret2 ,
             concat !
             (concat !
              ("monotonicity of lend violated: my monotonicity test", ": "),
              stringify ! ("x < y -> f(x) < f(y)"))) ;
        } 
        {
            debug_assert !
            (ret == format ! ("{}{}", ret3 . to_string(), ret4 . to_string()) .
             as_str(), concat !
             (concat !
              ("homomorphism of lend violated: my homomorphism test", ": "),
              stringify ! ("f(x) + f(y) = f(x + y)"))) ;
        } 
        {
            debug_assert !
            (ret == ret5, concat !
             (concat ! ("cyclicity of lend violated: my cyclicity test", ": "),
              stringify ! ("f(x + t) = f(x)"))) ;
        } assert !
        (ret == "a", concat !
         (concat ! ("Post-condition of lend violated", ": "), stringify !
          (ret == "a"))) ; ret
    }

    // {
    //     let book_id_contract_2 = format !
    //     ("{}{}", book_id . to_string(), "1" . to_string()) ; let
    //     book_id_contract_2 = book_id_contract_2 . as_str() ; let
    //     book_id_contract_3 = "1" ; let book_id_contract_4 = format !
    //     ("{}{}", book_id . to_string(), "1" . to_string()) ; let
    //     book_id_contract_4 = book_id_contract_4 . as_str() ; let
    //     book_id_contract_5 = format !
    //     ("{}{}", book_id . to_string(), "1" . to_string()) ; let
    //     book_id_contract_5 = book_id_contract_5 . as_str() ; let mut
    //     self_contract_1 = self . clone() ; let mut self_contract_2 = self .
    //     clone() ; let mut self_contract_3 = self . clone() ; let mut
    //     self_contract_4 = self . clone() ; let mut self_contract_5 = self .
    //     clone() ; debug_assert !
    //     (self . book_exist(book_id), concat !
    //      (concat ! ("Pre-condition of lend violated", ": "), stringify !
    //       (self . book_exist(book_id)))) ; #[allow(unused_mut)] let mut run = ||
    //     -> & str
    //     {
    //         if self . available . contains(book_id)
    //         {
    //             self . available . remove(book_id) ; self . lent .
    //             insert(book_id . to_string()) ; "a"
    //         } else { "b" }
    //     } ; let ret = run() ; let book_id_contract_1 = ret . clone() ;
    //     debug_assert !
    //     (self . book_exist(book_id_contract_1), concat !
    //      (concat ! ("Pre-condition of lend violated", ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run1 = || -> & str
    //     {
    //         if self_contract_1 . available . contains(book_id_contract_1)
    //         {
    //             self_contract_1 . available . remove(book_id_contract_1) ;
    //             self_contract_1 . lent . insert(book_id_contract_1 . to_string())
    //             ; "a"
    //         } else { "b" }
    //     } ; let ret1 = run1() ; debug_assert !
    //     (self . book_exist(book_id_contract_2), concat !
    //      (concat ! ("Pre-condition of lend violated", ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run2 = || -> & str
    //     {
    //         if self_contract_2 . available . contains(book_id_contract_2)
    //         {
    //             self_contract_2 . available . remove(book_id_contract_2) ;
    //             self_contract_2 . lent . insert(book_id_contract_2 . to_string())
    //             ; "a"
    //         } else { "b" }
    //     } ; let ret2 = run2() ; debug_assert !
    //     (self . book_exist(book_id_contract_3), concat !
    //      (concat ! ("Pre-condition of lend violated", ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run3 = || -> & str
    //     {
    //         if self_contract_3 . available . contains(book_id_contract_3)
    //         {
    //             self_contract_3 . available . remove(book_id_contract_3) ;
    //             self_contract_3 . lent . insert(book_id_contract_3 . to_string())
    //             ; "a"
    //         } else { "b" }
    //     } ; let ret3 = run3() ; debug_assert !
    //     (self . book_exist(book_id_contract_4), concat !
    //      (concat ! ("Pre-condition of lend violated", ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run4 = || -> & str
    //     {
    //         if self_contract_4 . available . contains(book_id_contract_4)
    //         {
    //             self_contract_4 . available . remove(book_id_contract_4) ;
    //             self_contract_4 . lent . insert(book_id_contract_4 . to_string())
    //             ; "a"
    //         } else { "b" }
    //     } ; let ret4 = run4() ; debug_assert !
    //     (self . book_exist(book_id_contract_5), concat !
    //      (concat ! ("Pre-condition of lend violated", ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run5 = || -> & str
    //     {
    //         if self_contract_5 . available . contains(book_id_contract_5)
    //         {
    //             self_contract_5 . available . remove(book_id_contract_5) ;
    //             self_contract_5 . lent . insert(book_id_contract_5 . to_string())
    //             ; "a"
    //         } else { "b" }
    //     } ; let ret5 = run5() ; #[cfg(test)]
    //     {
    //         debug_assert !
    //         (ret + ret == ret1 + book_id, concat !
    //          (concat !
    //           ("iter_consistency of lend violated: my iter consistency test",
    //            ": "), stringify ! ("f(f(x)) - f(x) = f(x) - x"))) ;
    //     } #[cfg(test)]
    //     {
    //         debug_assert !
    //         (ret < ret2, concat !
    //          (concat !
    //           ("monotonicity of lend violated: my monotonicity test", ": "),
    //           stringify ! ("x < y -> f(x) < f(y)"))) ;
    //     } #[cfg(test)]
    //     {
    //         debug_assert !
    //         (ret == ret3 + ret4, concat !
    //          (concat !
    //           ("homomorphism of lend violated: my homomorphism test", ": "),
    //           stringify ! ("f(x) + f(y) = f(x + y)"))) ;
    //     } #[cfg(test)]
    //     {
    //         debug_assert !
    //         (ret == ret5, concat !
    //          (concat ! ("cyclicity of lend violated: my cyclicity test", ": "),
    //           stringify ! ("f(x + t) = f(x)"))) ;
    //     } assert !
    //     (ret == "a", concat !
    //      (concat ! ("Post-condition of lend violated", ": "), stringify !
    //       (ret == "a"))) ; ret
    // }

    pub fn return_book(&mut self, book_id: String) -> String{
        String::from("")
    }
    
    // {
    //     let __contract_old_0 = self . lent . len() ; let book_id_contract_2 =
    //     book_id . clone() + "1" ; let book_id_contract_3 = "1" . to_string() ; ;
    //     let book_id_contract_4 = book_id . clone() + "1" ; let book_id_contract_5
    //     = book_id . clone() + "1" ; let mut self_contract_1 = self . clone() ; let
    //     mut self_contract_2 = self . clone() ; let mut self_contract_3 = self .
    //     clone() ; let mut self_contract_4 = self . clone() ; let mut
    //     self_contract_5 = self . clone() ; debug_assert !
    //     (self . lent . contains(& book_id), concat !
    //      (concat !
    //       ("Pre-condition of return_book violated: Can\'t return a non-lent book",
    //        ": "), stringify ! (self . lent . contains(& book_id)))) ;
    //     #[allow(unused_mut)] let mut run = || -> String
    //     {
    //         self . lent . remove(& book_id) ; self . available . insert(book_id) ;
    //         String :: from("OK")
    //     } ; let ret = run() ; let book_id_contract_1 = ret . clone() ;
    //     debug_assert !
    //     (self . lent . contains(& book_id_contract_1), concat !
    //      (concat !
    //       ("Pre-condition of return_book violated: Can\'t return a non-lent book",
    //        ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run1 = || -> String
    //     {
    //         self_contract_1 . lent . remove(& book_id_contract_1) ;
    //         self_contract_1 . available . insert(book_id_contract_1) ; String ::
    //         from("OK")
    //     } ; let ret1 = run1() ; debug_assert !
    //     (self . lent . contains(& book_id_contract_2), concat !
    //      (concat !
    //       ("Pre-condition of return_book violated: Can\'t return a non-lent book",
    //        ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run2 = || -> String
    //     {
    //         self_contract_2 . lent . remove(& book_id_contract_2) ;
    //         self_contract_2 . available . insert(book_id_contract_2) ; String ::
    //         from("OK")
    //     } ; let ret2 = run2() ; debug_assert !
    //     (self . lent . contains(& book_id_contract_3), concat !
    //      (concat !
    //       ("Pre-condition of return_book violated: Can\'t return a non-lent book",
    //        ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run3 = || -> String
    //     {
    //         self_contract_3 . lent . remove(& book_id_contract_3) ;
    //         self_contract_3 . available . insert(book_id_contract_3) ; String ::
    //         from("OK")
    //     } ; let ret3 = run3() ; debug_assert !
    //     (self . lent . contains(& book_id_contract_4), concat !
    //      (concat !
    //       ("Pre-condition of return_book violated: Can\'t return a non-lent book",
    //        ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run4 = || -> String
    //     {
    //         self_contract_4 . lent . remove(& book_id_contract_4) ;
    //         self_contract_4 . available . insert(book_id_contract_4) ; String ::
    //         from("OK")
    //     } ; let ret4 = run4() ; debug_assert !
    //     (self . lent . contains(& book_id_contract_5), concat !
    //      (concat !
    //       ("Pre-condition of return_book violated: Can\'t return a non-lent book",
    //        ": "), stringify !
    //       ("extra run input against the pre-condition input assumption"))) ;
    //     #[allow(unused_mut)] let mut run5 = || -> String
    //     {
    //         self_contract_5 . lent . remove(& book_id_contract_5) ;
    //         self_contract_5 . available . insert(book_id_contract_5) ; String ::
    //         from("OK")
    //     } ; let ret5 = run5() ; #[cfg(test)]
    //     {
    //         debug_assert !
    //         (ret + ret == ret1 + book_id, concat !
    //          (concat !
    //           ("iter_consistency of return_book violated: my iter consistency test",
    //            ": "), stringify ! ("f(f(x)) - f(x) = f(x) - x"))) ;
    //     } #[cfg(test)]
    //     {
    //         debug_assert !
    //         (ret < ret2, concat !
    //          (concat !
    //           ("monotonicity of return_book violated: my monotonicity test",
    //            ": "), stringify ! ("x < y -> f(x) < f(y)"))) ;
    //     } #[cfg(test)]
    //     {
    //         debug_assert !
    //         (ret == ret3 + ret4, concat !
    //          (concat !
    //           ("homomorphism of return_book violated: my homomorphism test",
    //            ": "), stringify ! ("f(x) + f(y) = f(x + y)"))) ;
    //     } #[cfg(test)]
    //     {
    //         debug_assert !
    //         (ret == ret5, concat !
    //          (concat !
    //           ("cyclicity of return_book violated: my cyclicity test", ": "),
    //           stringify ! ("f(x + t) = f(x)"))) ;
    //     } assert !
    //     (self . lent . len() == __contract_old_0 - 1, concat !
    //      (concat ! ("Post-condition of return_book violated", ": "), stringify !
    //       (self . lent . len() == old(self . lent . len()) - 1))) ; ret
    // }

    pub fn destory_book(&mut self, book: Book) -> Book
    {
        let __contract_old_0 = self . lent . len() ; let book_contract_1 = book .
        clone() ; let book_contract_1 = book_contract_1 . reverse() ; let
        book_contract_old = book . clone() ; let book_contract_3 = Book
        { id : 1, author : String :: from("bad boy") } ; let book_contract_4 =
        book . clone() ; let book_contract_4 = book_contract_4 .
        merge(Book { id : 1, author : String :: from("bad boy") }) ; let
        book_contract_5 = book . clone() ; let book_contract_5 = book_contract_5 .
        add(1) ; let mut self_contract_1 = self . clone() ; let mut
        self_contract_2 = self . clone() ; let mut self_contract_3 = self .
        clone() ; let mut self_contract_4 = self . clone() ; let mut
        self_contract_5 = self . clone() ; debug_assert !
        (self . lent . contains(& book . id . to_string()), concat !
         (concat !
          ("Pre-condition of destory_book violated: Can\'t return a non-lent book",
           ": "), stringify !
          (self . lent . contains(& book . id . to_string())))) ;
        #[allow(unused_mut)] let mut run = || -> Book
        {
            self . available . remove(& book . id . to_string()) ; book . add(1) ;
            Book { id : 1, author : String :: from("bad boy") }
        } ; let ret = run() ; debug_assert !
        (self . lent . contains(& book_contract_1 . id . to_string()), concat !
         (concat !
          ("Pre-condition of destory_book violated: Can\'t return a non-lent book",
           ": "), stringify !
          (self . lent . contains(& book . id . to_string())))) ;
        #[allow(unused_mut)] let mut run1 = || -> Book
        {
            self_contract_1 . available .
            remove(& book_contract_1 . id . to_string()) ; book_contract_1 .
            add(1) ; Book { id : 1, author : String :: from("bad boy") }
        } ; let ret1 = run1() ; let book_contract_2 = ret . clone() ; debug_assert
        !
        (self . lent . contains(& book_contract_2 . id . to_string()), concat !
         (concat !
          ("Pre-condition of destory_book violated: Can\'t return a non-lent book",
           ": "), stringify !
          (self . lent . contains(& book . id . to_string())))) ;
        #[allow(unused_mut)] let mut run2 = || -> Book
        {
            self_contract_2 . available .
            remove(& book_contract_2 . id . to_string()) ; book_contract_2 .
            add(1) ; Book { id : 1, author : String :: from("bad boy") }
        } ; let ret2 = run2() ; debug_assert !
        (self . lent . contains(& book_contract_3 . id . to_string()), concat !
         (concat !
          ("Pre-condition of destory_book violated: Can\'t return a non-lent book",
           ": "), stringify !
          (self . lent . contains(& book . id . to_string())))) ;
        #[allow(unused_mut)] let mut run3 = || -> Book
        {
            self_contract_3 . available .
            remove(& book_contract_3 . id . to_string()) ; book_contract_3 .
            add(1) ; Book { id : 1, author : String :: from("bad boy") }
        } ; let ret3 = run3() ; debug_assert !
        (self . lent . contains(& book_contract_4 . id . to_string()), concat !
         (concat !
          ("Pre-condition of destory_book violated: Can\'t return a non-lent book",
           ": "), stringify !
          (self . lent . contains(& book . id . to_string())))) ;
        #[allow(unused_mut)] let mut run4 = || -> Book
        {
            self_contract_4 . available .
            remove(& book_contract_4 . id . to_string()) ; book_contract_4 .
            add(1) ; Book { id : 1, author : String :: from("bad boy") }
        } ; let ret4 = run4() ; debug_assert !
        (self . lent . contains(& book_contract_5 . id . to_string()), concat !
         (concat !
          ("Pre-condition of destory_book violated: Can\'t return a non-lent book",
           ": "), stringify !
          (self . lent . contains(& book . id . to_string())))) ;
        #[allow(unused_mut)] let mut run5 = || -> Book
        {
            self_contract_5 . available .
            remove(& book_contract_5 . id . to_string()) ; book_contract_5 .
            add(1) ; Book { id : 1, author : String :: from("bad boy") }
        } ; let ret5 = run5() ;
        {
            debug_assert !
            (ret == ret1, concat !
             (concat !
              ("symmetry of destory_book violated: my symmetry test", ": "),
              stringify ! ("f(x) = ±f(2*y - x)"))) ;
        }
        {
            debug_assert !
            (ret . clone() . merge(ret . clone()) == ret2 . clone() .
             merge(book_contract_old . clone()), concat !
             (concat !
              ("iter_consistency of destory_book violated: my iter consistency test",
               ": "), stringify ! ("f(f(x)) - f(x) = f(x) - x"))) ;
        }
        {
            debug_assert !
            (ret == ret3 . clone() . merge(ret4 . clone()), concat !
             (concat !
              ("homomorphism of destory_book violated: my homomorphism test",
               ": "), stringify ! ("f(x) + f(y) = f(x + y)"))) ;
        }
        {
            debug_assert !
            (ret == ret5, concat !
             (concat !
              ("cyclicity of destory_book violated: my cyclicity test", ": "),
              stringify ! ("f(x + t) = f(x)"))) ;
        } assert !
        (self . lent . len() == __contract_old_0 - 1, concat !
         (concat ! ("Post-condition of destory_book violated", ": "), stringify !
          (self . lent . len() == old(self . lent . len()) - 1))) ; ret
    }

    pub fn change_book(&mut self, book: &Book) -> Book
    {
        let mut book_contract_1 = book . clone() ; let book_contract_1 =
        book_contract_1 . ref_add(1) ; let mut self_contract_1 = self . clone() ;
        #[allow(unused_mut)] let mut run = || -> Book
        {
            self . available . insert(book . id . to_string()) ; Book
            { id : 1, author : String :: from("bad boy") }
        } ; let ret = run() ; #[allow(unused_mut)] let mut run1 = || -> Book
        {
            self_contract_1 . available .
            insert(book_contract_1 . id . to_string()) ; Book
            { id : 1, author : String :: from("bad boy") }
        } ; let ret1 = run1() ;
        {
            debug_assert !
            (ret == ret1, concat !
             (concat !
              ("cyclicity of change_book violated: my cyclicity test", ": "),
              stringify ! ("f(x + t) = f(x)"))) ;
        } ret
    }
}

fn main() {
    let mut lib = Library {
        available: HashSet::new(),
        lent: HashSet::new(),
    };

    let book_id = 1;
    lib.add_book( book_id);
}