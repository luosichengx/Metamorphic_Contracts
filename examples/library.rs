/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use contracts::*;

use std::collections::HashSet;

#[derive(Clone, Eq, PartialEq, Debug)]
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
    #[allow(dead_code)]
    // #[ensures(self == old(self), "No change")]
    fn book_exists(&self, book_id:  usize) -> bool {
        self.available.contains(&book_id.to_string()) || self.lent.contains(&book_id.to_string())
    }

    #[allow(dead_code)]
    // #[ensures(self == old(self), "No change")]
    fn book_exist(&self, book_id:  &str) -> bool {
        self.available.contains(book_id) || self.lent.contains(book_id)
    }

    // #[debug_requires(!self.book_exists(book_id), "Book IDs are unique")]
    // // #[debug_ensures(self.available.contains(book_id), "Book now available")]
    // #[ensures(self.available.len() == old(self.available.len()) + 1)]
    // // #[ensures(self.lent.len() == old(self.lent.len()), "No lent change")]
    // #[iter_consistency(book_id, +, "my iter consistency test")]
    // // #[symmetry(book_id, 1, -, "my symmetry test")]
    // #[monotonicity(book_id, 1, <, "my monotonicity test")]
    // #[homomorphism(book_id, 1, +, "my homomorphism test")]
    // #[cyclicity(book_id, 1, +, "my cyclicity test")]
    // // #[local_invariance(book_id, 1, "my add equal test")]
    // pub fn add_book(&mut self, book_id: usize) -> usize{
    //     self.available.insert((book_id + 1).to_string());
    //     self.available.len()
    // }

    // #[debug_requires(self.book_exist(book_id))]
    // #[ensures(ret == "a")]
    // #[iter_consistency(book_id, +, "my iter consistency test")]
    // // #[symmetry(book_id, "1", -, "my symmetry test")]
    // #[monotonicity(book_id, "1", <, "my monotonicity test")]
    // #[homomorphism(book_id, "1", +, "my homomorphism test")]
    // #[cyclicity(book_id, "1", +, "my cyclicity test")]
    // pub fn lend(&mut self, book_id: &str) -> &str {
    //     if self.available.contains(book_id) {
    //         self.available.remove(book_id);
    //         self.lent.insert(book_id.to_string());
    //         "a"
    //     } else {
    //         "b"
    //     }
    // }

    // #[debug_requires(self.book_exists(book_id))]
    // #[ensures(ret -> self.available.len() == old(self.available.len()) - 1)]
    // #[ensures(ret -> self.lent.len() == old(self.lent.len()) + 1)]
    // #[debug_ensures(ret -> self.lent.contains(book_id))]
    // #[debug_ensures(!ret -> self.lent.contains(book_id), "Book already lent")]
    // pub fn lend(&mut self, book_id: &str) -> bool {
    //     if self.available.contains(book_id) {
    //         self.available.remove(book_id);
    //         self.lent.insert(book_id.to_string());
    //         true
    //     } else {
    //         false
    //     }
    // }

    // #[debug_requires(self.lent.contains(&book_id), "Can't return a non-lent book")]
    // #[ensures(self.lent.len() == old(self.lent.len()) - 1)]
    // #[iter_consistency(book_id, +, "my iter consistency test")]
    // #[monotonicity(book_id, "1", <, "my monotonicity test")]
    // #[homomorphism(book_id, "1", +, "my homomorphism test")]
    // #[cyclicity(book_id, "1", +, "my cyclicity test")]
    // pub fn return_book(&mut self, book_id: String) -> String{
    //     self.lent.remove(&book_id);
    //     self.available.insert(book_id);
    //     String::from("OK")
    // }

    // #[debug_requires(self.lent.contains(&book.id.to_string()), "Can't return a non-lent book")]
    // #[ensures(self.lent.len() == old(self.lent.len()) - 1)]
    // #[symmetry(book, reverse, +, "my symmetry test")]
    // #[iter_consistency(book, merge, "my iter consistency test")]
    // // #[monotonicity(book, 1, add, "my monotonicity test")] not implemented since it need two operators
    // #[homomorphism(book, Book{id:1, author:String::from("bad boy")}, merge, "my homomorphism test")]
    // #[cyclicity(book, 1, add, "my cyclicity test")]
    // pub fn destory_book(&mut self, book: Book) -> Book{
    //     self.available.remove(&book.id.to_string());
    //     book.add(1);
    //     Book{id:1,author:String::from("bad boy")}
    // }

    // #[debug_requires(self.lent.contains(&book.id.to_string()), "Can't return a non-lent book")]
    // #[ensures(self.lent.len() == old(self.lent.len()) - 1)]
    // #[symmetry(book, ref_reverse, +, "my symmetry test")]
    // #[iter_consistency(book, ref_merge, "my iter consistency test")]
    // #[monotonicity(book, 1, ref_add, "my monotonicity test")]
    // #[homomorphism(book, Book{id:1, author:String::from("bad boy")}, ref_merge, "my homomorphism test")]
    // #[cyclicity(book, 1, ref_add, "my cyclicity test")]
    pub fn change_book(&mut self, book: &Book) -> Book{
        self.available.insert(book.id.to_string());
        Book{id:1,author:String::from("bad boy")}
    }
}

fn main() {
    let lib = Library {
        available: HashSet::new(),
        lent: HashSet::new(),
    };

    // let book_id = "Das Kapitala";
    let book_id = 1;
    println!("{:?}", lib);
    // lib.add_book(book_id);
    // lib.add_book("Das Kapital");
    println!("Adding a book {}.", book_id);
    // let lent_successful = lib.lend("Das Kapital");
    // assert_eq!(lent_successful, true);

    // if lent_successful {
    //     println!("Lent out the book.");
    //     println!("Reading for a bit...");

    //     println!("Giving back the book.");

    //     lib.return_book("Das Kapital");
    // }
}
