target "x86_64-linux-userspace";
runtime "modeled-pthread";
verifying "publication.c";

resource ready_payload(channel: struct channel*) {
    owns channel->payload;
    fact channel->payload == 42;
}

void* producer(void* argument) {
    consumes publisher(
        &((struct channel*)argument)->ready,
        ready_payload((struct channel*)argument)
    );
    consumes ((struct channel*)argument)->payload;
    ensures result == 0;
} by {
    step();
    step();
    step();
    fold(ready_payload(channel));
    step();
    step();
    simp();
}

int32 consume(struct channel* channel) diverges {
    consumes subscriber(&channel->ready, ready_payload(channel));
    produces ready_payload(channel);
    ensures result == 42;
} by {
    loop diverges {
        owns subscriber(&channel->ready, ready_payload(channel));
    }
    unfold(ready_payload(channel));
    step();
    fold(ready_payload(channel));
    simp();
}

int32 publish_once(struct channel* channel) diverges {
    consumes channel->ready;
    owns channel->payload;
    requires aligned(&channel->ready, 4);
    ensures result == 42 or result == -1;
} by {
    step();
    step();
    step(atomic_init(&channel->ready, 0), { payload: ready_payload(channel) });
    step();
    branch then {
        step();
        simp();
    } else {}
    step();
    step();
    unfold(ready_payload(channel));
    step();
    simp();
}
