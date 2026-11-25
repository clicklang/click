verifying "sequence_transform.c";

void sequence_copy3(int32 destination[], int32 source[]) {
    owns destination[0..3];
    views source[0..3];
    requires separate(memory(destination[0..3]), memory(source[0..3]));

    ensures [destination[0], destination[1], destination[2]]
        == old([source[0], source[1], source[2]]);
} by {
    have separate(memory(destination[0]), memory(source[1])) by { close(); }
    have separate(memory(destination[0]), memory(source[2])) by { close(); }
    step();
    have separate(statement(0).footprint, memory(source[1])) by {
        close() using { separate(memory(destination[0]), memory(source[1])); };
    }
    have at(statement(0).exit, source[1]) == at(statement(0).entry, source[1]) by {
        preserve(memory(source[1]), statement(0));
    }
    have separate(statement(0).footprint, memory(source[2])) by {
        close() using { separate(memory(destination[0]), memory(source[2])); };
    }
    have at(statement(0).exit, source[2]) == at(statement(0).entry, source[2]) by {
        preserve(memory(source[2]), statement(0));
    }
    have separate(memory(destination[1]), memory(source[2])) by { close(); }
    step();
    have separate(statement(1).footprint, memory(source[2])) by {
        close() using { separate(memory(destination[1]), memory(source[2])); };
    }
    have at(statement(1).exit, source[2]) == at(statement(1).entry, source[2]) by {
        preserve(memory(source[2]), statement(1));
    }
    step();
    step();
    close();
}

void sequence_concatenate2(
    int32 destination[],
    int32 left[],
    int32 right[]
) {
    owns destination[0..4];
    views left[0..2];
    views right[0..2];
    requires separate(memory(destination[0..4]), memory(left[0..2]));
    requires separate(memory(destination[0..4]), memory(right[0..2]));

    ensures [destination[0], destination[1]]
            ++ [destination[2], destination[3]]
        == old([left[0], left[1]] ++ [right[0], right[1]]);
} by {
    have separate(memory(destination[0]), memory(left[1])) by { close(); }
    have separate(memory(destination[0]), memory(right[0])) by { close(); }
    have separate(memory(destination[0]), memory(right[1])) by { close(); }
    step();
    have separate(statement(0).footprint, memory(left[1])) by {
        close() using { separate(memory(destination[0]), memory(left[1])); };
    }
    have at(statement(0).exit, left[1]) == at(statement(0).entry, left[1]) by {
        preserve(memory(left[1]), statement(0));
    }
    have separate(statement(0).footprint, memory(right[0])) by {
        close() using { separate(memory(destination[0]), memory(right[0])); };
    }
    have at(statement(0).exit, right[0]) == at(statement(0).entry, right[0]) by {
        preserve(memory(right[0]), statement(0));
    }
    have separate(statement(0).footprint, memory(right[1])) by {
        close() using { separate(memory(destination[0]), memory(right[1])); };
    }
    have at(statement(0).exit, right[1]) == at(statement(0).entry, right[1]) by {
        preserve(memory(right[1]), statement(0));
    }
    have separate(memory(destination[1]), memory(right[0])) by { close(); }
    have separate(memory(destination[1]), memory(right[1])) by { close(); }
    step();
    have separate(statement(1).footprint, memory(right[0])) by {
        close() using { separate(memory(destination[1]), memory(right[0])); };
    }
    have at(statement(1).exit, right[0]) == at(statement(1).entry, right[0]) by {
        preserve(memory(right[0]), statement(1));
    }
    have separate(statement(1).footprint, memory(right[1])) by {
        close() using { separate(memory(destination[1]), memory(right[1])); };
    }
    have at(statement(1).exit, right[1]) == at(statement(1).entry, right[1]) by {
        preserve(memory(right[1]), statement(1));
    }
    have separate(memory(destination[2]), memory(right[1])) by { close(); }
    step();
    have separate(statement(2).footprint, memory(right[1])) by {
        close() using { separate(memory(destination[2]), memory(right[1])); };
    }
    have at(statement(2).exit, right[1]) == at(statement(2).entry, right[1]) by {
        preserve(memory(right[1]), statement(2));
    }
    step();
    step();
    close();
}

void sequence_reverse3(int32 values[]) {
    owns values[0..3];

    ensures [values[0], values[1], values[2]]
        == old([values[2], values[1], values[0]]);
}

int32 sequence_contains3(int32 values[], int32 target) {
    views values[0..3];

    ensures result != 0 implies target in old([values[0], values[1], values[2]]);
    ensures target in old([values[0], values[1], values[2]]) implies result != 0;
} by {
    if values[0] == target {
        step_until(function.exit);
    } else {
        if values[1] == target {
            step_until(function.exit);
        } else {
            if values[2] == target {
                step_until(function.exit);
            } else {
                step_until(function.exit);
                if target in [values[0], values[1], values[2]] {
                    close();
                } else {
                    close();
                }
            }
        }
    }
}
