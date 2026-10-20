verifying "holders.rs";

// Every holder holds one value: what is put is what is got.
trait generic_state::Holder<T> {
    function held(self) -> T;
    fn put(&mut self, x: T) {
        ensures held(self) == x;
    }
    fn get(&self) -> T {
        ensures result == held(self);
    }
}

// One implementation for every type, verified once with `T` abstract. Its
// object is `Holder::object<T>`, at `u32` and `i32` where the callers pack
// a `Wrap<u32>` and a `Wrap<i32>`.
impl<T: Copy> generic_state::Holder<T> for generic_state::Wrap<T> {
    function held(self) -> T { self.value }
    fn put(&mut self, x: T) {
    } by { execute(); simp(); }
    fn get(&self) -> T {
    } by { execute(); simp(); }
}

fn generic_state::store<H: generic_state::Holder<u32>>(holder: &mut H, x: u32) -> u32 {
    ensures result == x;
    ensures held(holder) == x;
} by { execute(); simp(); }

fn generic_state::store_dyn(holder: &mut dyn generic_state::Holder<u32>, x: u32) -> u32 {
    ensures result == x;
    ensures held(holder) == x;
} by { execute(); simp(); }

fn generic_state::peek<H: generic_state::Holder<i32>>(holder: &H) -> i32 {
    ensures result == held(holder);
} by { execute(); simp(); }

// The callers lend a `Wrap<u32>` as the holder's object and get back a
// struct whose `value` is the object's new state.
fn generic_state::through(x: u32) -> u32 {
    ensures result == x;
} by { execute(); simp(); }

fn generic_state::through_dyn(x: u32) -> u32 {
    ensures result == x;
} by { execute(); simp(); }

// A shared `Wrap<i32>` keeps every field, `puts` included.
fn generic_state::through_peek(level: i32) -> u32 {
    ensures result == 7;
} by { execute(); simp(); }
