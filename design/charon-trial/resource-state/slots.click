verifying "slots.rs";

// The value an option holds, or `fallback`.
function value_or<T>(o: Option<T>, fallback: T) -> T {
    match o {
        Option::Some(v) => v,
        Option::None => fallback,
    }
}

// Every store holds at most one value: what is put is taken back.
trait resource_state::Store<T> {
    function item(self) -> Option<T>;
    fn put(&mut self, x: T) {
        ensures item(self) == Option<T>::Some(x);
    }
    fn take_or(&mut self, fallback: T) -> T {
        ensures result == value_or(old(item(self)), fallback);
        ensures item(self) == Option<T>::None;
    }
}

// A `Slot`'s value is not in the struct but in the box its field points
// at, or nowhere: a resource over the allocation holds it.
resource boxed(p: *mut resource_state::Cell) {
    field value: Option<u32>;
    match value {
        Option::None => { fact p == 0; },
        Option::Some(v) => {
            owns allocation(p, sizeof(resource_state::Cell));
            owns *p;
            fact p != 0;
            fact p.value == v;
        },
    }
}

// The implementation names the resource holding its object's state,
// `state`, and defines the trait's function from it.
impl resource_state::Store<u32> for resource_state::Slot {
    resource state: boxed(self.item);
    function item(self) -> Option<u32> { state.value }
    fn put(&mut self, x: u32) {
    } by {
        match state.value {
            Option::None => {
                let {} = unfold(state);
                execute();
                let state = fold(boxed(self.item), { value: Option<u32>::Some(x) }, {});
            }
            Option::Some(v) => {
                let {} = unfold(state);
                execute();
                let state = fold(boxed(self.item), { value: Option<u32>::Some(x) }, {});
            }
        }
    }
    fn take_or(&mut self, fallback: u32) -> u32 {
    } by {
        match state.value {
            Option::None => {
                let {} = unfold(state);
                execute();
                let state = fold(boxed(self.item), { value: Option<u32>::None }, {});
                simp();
            }
            Option::Some(v) => {
                let {} = unfold(state);
                execute();
                let state = fold(boxed(self.item), { value: Option<u32>::None }, {});
                simp();
            }
        }
    }
}

fn resource_state::refill<S: resource_state::Store<u32>>(store: &mut S, x: u32) -> u32 {
    ensures result == x;
    ensures item(store) == Option<u32>::None;
} by {
    execute();
    unfold(value_or(Option<u32>::Some(x), 0u32));
    simp();
}

fn resource_state::refill_dyn(store: &mut dyn resource_state::Store<u32>, x: u32) -> u32 {
    ensures result == x;
    ensures item(store) == Option<u32>::None;
} by {
    execute();
    unfold(value_or(Option<u32>::Some(x), 0u32));
    simp();
}

// A caller lends its `Slot` with the box's resource: both become the
// store's object, and come back as a `boxed` instance holding the value the
// object ends with, which the caller's `state` takes at its exit.
fn resource_state::through(slot: &mut resource_state::Slot, x: u32) -> u32 {
    owns *slot;
    owns state: boxed(slot.item);
    ensures result == x;
    ensures state.value == Option<u32>::None;
} by { execute(); simp(); }

fn resource_state::through_dyn(slot: &mut resource_state::Slot, x: u32) -> u32 {
    owns *slot;
    owns state: boxed(slot.item);
    ensures result == x;
    ensures state.value == Option<u32>::None;
} by { execute(); simp(); }
