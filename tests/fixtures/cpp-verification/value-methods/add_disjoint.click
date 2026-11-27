verifying "value_methods.cpp";

void FeeFrac::operator+=(const FeeFrac& other) {
    owns this->fee;
    owns this->size;
    owns other.fee;
    owns other.size;
    requires -4611686018427387904 <= this->fee;
    requires this->fee <= 4611686018427387903;
    requires -4611686018427387904 <= other.fee;
    requires other.fee <= 4611686018427387903;
    requires -1073741824 <= this->size;
    requires this->size <= 1073741823;
    requires -1073741824 <= other.size;
    requires other.size <= 1073741823;
    ensures this->fee == old(this->fee) + old(other.fee);
    ensures this->size == old(this->size) + old(other.size);
    ensures other.fee == old(other.fee);
    ensures other.size == old(other.size);
} by {
    step();
    have this->size == old(this->size) by { close(); }
    // Frame the typed cells. The final size field's owned range also covers padding.
    have separate(memory(this->fee), memory((&other.size)[0..1]));
    have separate(region(0).footprint, memory((&other.size)[0..1])) by close() using {
        separate(memory(this->fee), memory((&other.size)[0..1]));
    };
    have at(region(0).exit, other.size) == at(region(0).entry, other.size) by {
        preserve(memory((&other.size)[0..1]), region(0));
    }
    have other.size == old(other.size) by close() using {
        at(region(0).exit, other.size) == at(region(0).entry, other.size);
    };
    have -1073741824 <= this->size by { close(); }
    have this->size <= 1073741823 by { close(); }
    have -1073741824 <= other.size by { close(); }
    have other.size <= 1073741823 by { close(); }
    have separate(memory(this->fee), memory((&other.fee)[0..1]));
    have separate(region(0).footprint, memory((&other.fee)[0..1]));
    have other.fee == at(region(0).entry, other.fee) by {
        preserve(memory((&other.fee)[0..1]), region(0));
    }
    have other.fee == old(other.fee);
    step_until(function.exit);
    have separate(memory((&this->size)[0..1]), memory((&other.fee)[0..1]));
    have separate(memory((&this->size)[0..1]), memory((&other.size)[0..1]));
    have separate(region(1).footprint, memory((&other.fee)[0..1])) by close() using {
        separate(memory((&this->size)[0..1]), memory((&other.fee)[0..1]));
    };
    have separate(region(1).footprint, memory((&other.size)[0..1])) by close() using {
        separate(memory((&this->size)[0..1]), memory((&other.size)[0..1]));
    };
    have other.fee == at(region(1).entry, other.fee) by {
        preserve(memory((&other.fee)[0..1]), region(1));
    }
    have other.size == at(region(1).entry, other.size) by {
        preserve(memory((&other.size)[0..1]), region(1));
    }
    close();
}
