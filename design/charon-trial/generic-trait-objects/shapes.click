verifying "shapes.rs";
import click::list;

// Generic crate traits whose objects carry state: the generic block's
// `function`s are each instance's object fields, at the instance's types.

// Every bag: inserting counts the element and makes it the last one.
trait bags::Bag<T> {
    function count(self) -> u32;
    function last(self) -> T;
    fn insert(&mut self, x: T) {
        requires count(self) < 1000;
        ensures count(self) == old(count(self)) + 1;
        ensures last(self) == x;
    }
    fn size(&self) -> u32 {
        ensures result == count(self);
    }
}

impl bags::Bag<i32> for bags::Counter {
    function count(self) -> u32 { self.count }
    function last(self) -> i32 { self.last }
    fn insert(&mut self, x: i32) {
    } by { execute(); simp(); }
    fn size(&self) -> u32 {
    } by { execute(); simp(); }
}

fn bags::fill<B: bags::Bag<i32>>(bag: &mut B, x: i32) -> u32 {
    requires count(bag) < 1000;
    ensures result == old(count(bag)) + 1;
    ensures last(bag) == x;
} by { execute(); simp(); }

fn bags::fill_dyn(bag: &mut dyn bags::Bag<i32>, x: i32) -> u32 {
    requires count(bag) < 1000;
    ensures result == old(count(bag)) + 1;
    ensures last(bag) == x;
} by { execute(); simp(); }

fn bags::through_fill(x: i32) -> u32 {
    ensures result == 1;
} by { execute(); simp(); }

fn bags::through_dyn(x: i32) -> i32 {
    ensures result == x;
} by { execute(); simp(); }

// Every holder: what is put is among its items.
trait bags::Holder<T> {
    function items(self) -> List<T>;
    fn put(&mut self, x: T) {
        ensures list::contains(items(self), x);
    }
}

impl bags::Holder<i32> for bags::Slot {
    function items(self) -> List<i32> {
        List<i32>::Cons(self.value, List<i32>::Nil)
    }
    fn put(&mut self, x: i32) {
    } by { execute(); simp(); }
}

fn bags::store<H: bags::Holder<i32>>(holder: &mut H, x: i32) {
    ensures list::contains(items(holder), x);
} by { execute(); simp(); }

// The caller lends a `Slot` as the holder's object, packed with its
// definition of `items`.
fn bags::through_store(x: i32) -> i32 {
    ensures result == x;
} by { execute(); simp(); }
