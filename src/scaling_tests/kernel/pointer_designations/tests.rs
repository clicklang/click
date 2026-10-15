// Deterministic scaling coverage for the independent designation index.
use super::*;
use crate::kernel::*;

#[test]
fn designation_queries_and_withdrawal_ignore_unrelated_origins() {
    let mut measurements = Vec::new();
    for size in [16u64,64,256,1024] {
        let mut classes = ValueClasses::<u64>::default();
        classes.insert(&1,&2,|a,_|*a);
        classes.insert(&2,&3,|a,_|*a);
        for index in 0..size {
            classes.insert(&(10+index*2),&(11+index*2),|a,_|*a);
        }
        let (_,work)=crate::instrumentation::measure_deterministic_work(|| {
            assert!(classes.equal(&1,&3));
            classes.remove(&1,&2,|a,_|*a);
            assert!(!classes.equal(&1,&3));
            assert!(classes.equal(&2,&3));
        });
        measurements.push(work);
    }
    assert!(measurements.iter().all(|work| *work==measurements[0]),"{measurements:?}");
}

#[test]
fn typed_access_does_not_search_unrelated_address_equalities_or_ranges() {
    let value=|id| CPointerValue::new(Pointer::symbolic(Variable(id)),CType::Int32Pointer);
    let a=value(870_001); let b=value(870_002);
    let mut samples=Vec::new();
    for size in [16u64,64,256,1024] {
        let mut context=PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(a.pointer().clone(),b.pointer().clone()),true);
        let mut resources=ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::from_pointer_value(&b,0u32.into(),1u32.into(),4)));
        for index in 0..size {
            let unrelated=value(880_000+index*2);
            context=context.assume_condition(ConditionTerm::pointer_equal(
                unrelated.pointer().clone(),value(880_001+index*2).pointer().clone()),true);
            resources=resources.unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::from_pointer_value(&unrelated,0u32.into(),1u32.into(),4)));
        }
        let (_,work)=crate::instrumentation::measure_deterministic_work(|| {
            assert!(resources.permits_designated_memory_read(b.pointer(),Some(b.designation()),4,&context));
            assert!(!resources.permits_designated_memory_read(a.pointer(),Some(a.designation()),4,&context));
        });
        samples.push(work);
    }
    assert!(samples[3]<=samples[0]*4+32,"{samples:?}");
}
