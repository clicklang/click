// Scaling tests of `src/languages/c/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// A static-storage array's initializer is held as what it wrote, whatever
/// the array's declared length: a tentative definition lists no element, a
/// partial or designated initializer (one- or multidimensional, file-scope
/// or static local) lists the elements it names, and lowering to the kernel
/// costs those elements. Every array used to hold, copy and lower one
/// expression per declared element, so four million-element arrays cost
/// seconds before verification began.
#[test]
fn c0_static_array_initializers_cost_what_they_write_whatever_the_length() {
    let samples = [100u32, 10_000, 1_000_000].map(|length| {
        let source = format!(
            "int32 buf[{length}];
            int32 table[{length}] = {{1, 2, [{last}] = 7}};
            static int32 grid[{rows}][10] = {{{{4}}, {{5, 6}}}};
            int32 read() {{
                static uint8 counts[{length}] = {{[7] = 5}};
                return buf[0] + table[0] + grid[0][0] + counts[7];
            }}",
            last = length - 1,
            rows = length / 10,
        );
        let functions = syntax::parse_functions(&source).expect("large arrays should parse");
        let function = &functions[0];
        let written = |initializer: &syntax::C0ArrayInitializer| {
            assert_eq!(initializer.length(), length);
            initializer.elements().to_vec()
        };
        let arrays = function.global_arrays();
        let listed = [
            written(arrays["buf"].initializer().expect("tentative storage")),
            written(arrays["table"].initializer().expect("definition")),
            written(arrays["grid"].initializer().expect("definition")),
            written(
                function
                    .static_arrays()
                    .values()
                    .next()
                    .expect("static array")
                    .initializer(),
            ),
        ];
        let (kernel, work) =
            crate::instrumentation::measure_deterministic_work(|| function.to_kernel_function());
        let kernel_listed = kernel
            .global_arrays()
            .iter()
            .map(|array| array.initial_values().explicit_elements().len())
            .chain(
                kernel
                    .static_arrays()
                    .iter()
                    .map(|array| array.initial_values().explicit_elements().len()),
            )
            .collect::<Vec<_>>();
        let table = kernel
            .global_arrays()
            .iter()
            .find(|array| array.name() == "table")
            .expect("kernel table")
            .initial_values();
        assert_eq!(
            [
                table.value_at(1),
                table.value_at(2),
                table.value_at(length - 1)
            ],
            [
                &crate::kernel::int32(2),
                &crate::kernel::int32(0),
                &crate::kernel::int32(7)
            ],
            "[{length}] table contents"
        );
        (length, listed, kernel_listed, work)
    });
    let (_, listed, kernel_listed, work) = &samples[0];
    assert_eq!(
        listed,
        &[
            vec![],
            vec![
                (0, syntax::C0Expression::Int32Literal(1)),
                (1, syntax::C0Expression::Int32Literal(2)),
                (99, syntax::C0Expression::Int32Literal(7)),
            ],
            vec![
                (0, syntax::C0Expression::Int32Literal(4)),
                (10, syntax::C0Expression::Int32Literal(5)),
                (11, syntax::C0Expression::Int32Literal(6)),
            ],
            vec![(7, syntax::C0Expression::UInt32Literal(5))],
        ]
    );
    assert!(
        samples.iter().all(|sample| {
            sample
                .1
                .iter()
                .map(Vec::len)
                .eq(listed.iter().map(Vec::len))
                && (&sample.2, sample.3) == (kernel_listed, *work)
        }),
        "an initializer's representation or lowering depends on its array's length \
         (length, written elements, kernel elements, lowering work): {samples:?}"
    );
}

/// An array of structs at file scope or `static`, and an automatic scalar or
/// struct array declared with an initializer, cost what their initializers
/// write, not their declared length: the static arrays list their written
/// fields, an automatic array's declaration carries one zero fill and is
/// followed only by the stores of the elements its initializer writes, and
/// lowering does the same work whatever the length. An automatic array
/// declared without an initializer carries no zero fill.
#[test]
fn c0_aggregate_and_automatic_array_initializers_cost_what_they_write_whatever_the_length() {
    let samples = [100u32, 10_000, 1_000_000].map(|length| {
        let source = format!(
            "struct node {{
                int32 key;
                struct node *next;
            }};
            struct node pool[{length}] = {{[3] = {{5}}}};
            int32 read() {{
                static struct node slots[{length}];
                int32 buf[{length}] = {{1, 0, 3}};
                struct node items[{length}] = {{{{4}}, {{0}}}};
                int32 scratch[{length}];
                scratch[0] = 1;
                return pool[3].key + slots[0].key + buf[2] + items[0].key + scratch[0];
            }}"
        );
        let functions = syntax::parse_functions(&source).expect("large arrays should parse");
        let function = &functions[0];
        let pool = function.global_aggregate_arrays()["pool"]
            .initializer()
            .expect("definition")
            .len();
        let slots = function
            .static_aggregate_arrays()
            .values()
            .next()
            .expect("static aggregate array")
            .initializer()
            .len();
        let mut zero_filled = Vec::new();
        let mut pending = vec![function.body()];
        while let Some(statement) = pending.pop() {
            match statement {
                syntax::C0Statement::Seq(first, second) => {
                    pending.push(first);
                    pending.push(second);
                }
                syntax::C0Statement::Declare {
                    name, zero_fill, ..
                } => zero_filled.push((name.clone(), zero_fill.is_some())),
                _ => {}
            }
        }
        zero_filled.sort();
        let statements = c0_statement_count(function.body());
        let (_, work) =
            crate::instrumentation::measure_deterministic_work(|| function.to_kernel_function());
        (length, pool, slots, zero_filled, statements, work)
    });
    let (_, pool, slots, zero_filled, statements, work) = &samples[0];
    assert_eq!((*pool, *slots), (1, 0), "only pool[3].key is listed");
    assert_eq!(
        zero_filled,
        &[
            ("buf".to_string(), true),
            ("items".to_string(), true),
            ("scratch".to_string(), false),
        ],
        "an automatic array zero-fills exactly when it has an initializer"
    );
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, &sample.3, sample.4, sample.5)
                == (*pool, *slots, zero_filled, *statements, *work)),
        "an initializer's representation or lowering depends on its array's length \
         (length, pool fields, slots fields, zero fills, body statements, lowering work): \
         {samples:?}"
    );
}
