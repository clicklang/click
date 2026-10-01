//! Fixed scalar arrays use ordinary automatic storage and checked aggregate
//! copies. Constructor operands are captured before any destination write.
use super::*;

fn array_type(element: CType, length: u64) -> Result<CType, String> {
    if !matches!(element, CType::UInt8 | CType::UInt32 | CType::Int32) {
        return Err("fixed arrays require i32, u8 or u32 elements".into());
    }
    if length > i32::MAX as u64 / u64::from(element.byte_width()) {
        return Err("fixed array storage exceeds the signed-word memory model".into());
    }
    let length = u32::try_from(length).map_err(|_| "array length exceeds modeled storage")?;
    match element {
        CType::UInt8 => Ok(CType::UInt8Array(length)),
        CType::UInt32 => Ok(CType::UInt32Array(length)),
        CType::Int32 => Ok(CType::Int32Array(length)),
        _ => Err("fixed arrays require i32, u8 or u32 elements".into()),
    }
}

impl Context<'_> {
    pub(super) fn declare_array(
        &mut self,
        name: &str,
        element: &Type,
        length: u64,
        initializer: &E,
    ) -> Result<CStatement, String> {
        let element = scalar_type(element)?.to_kernel_type();
        let array_type = array_type(element, length)?;
        self.local_arrays.insert(name.into());
        self.arrays.insert(name.into(), (length, element, false));
        Ok(c_seq(
            c_declare(name, array_type),
            self.assign_array(c_variable(name), element, length, initializer)?,
        ))
    }

    pub(super) fn assign_array(
        &mut self,
        target: CExpression,
        element: CType,
        length: u64,
        value: &E,
    ) -> Result<CStatement, String> {
        array_type(element, length)?;
        let source_type = match element {
            CType::UInt8 => Type::U8,
            CType::UInt32 => Type::U32,
            CType::Int32 => Type::I32,
            _ => return Err("unsupported fixed array element".into()),
        };
        let mut captures = c_skip();
        let mut values = Vec::new();
        match value {
            E::Array { elements } => {
                if elements.len() as u64 != length {
                    return Err("array constructor length disagrees with destination".into());
                }
                for e in elements {
                    let (prefix, value) = self.prepared_expr(e)?;
                    let (capture, name) = self.capture_operand(value, &source_type)?;
                    captures = c_seq(captures, c_seq(prefix, capture));
                    values.push(c_variable(name));
                }
            }
            E::Repeat {
                value,
                length: count,
            } => {
                if *count != length {
                    return Err("array repeat length disagrees with destination".into());
                }
                // Rust evaluates the operand once, even for a zero count.
                let (prefix, value) = self.prepared_expr(value)?;
                let (capture, name) = self.capture_operand(value, &source_type)?;
                captures = c_seq(prefix, capture);
                values.resize(length as usize, c_variable(name));
            }
            _ => {
                let (source, source_length, source_element) = self.indexed_parts(value)?;
                if source_length != c_uint64_literal(length) || source_element != element {
                    return Err("whole-array copy disagrees with destination type".into());
                }
                if length == 0 {
                    return Ok(c_skip());
                }
                let width = element.byte_width();
                let fields = (0..length as u32)
                    .map(|i| CAggregateField::new(i.to_string(), i * width, element))
                    .collect();
                return Ok(c_copy_aggregate(
                    target,
                    source,
                    CAggregateLayout::new(length as u32 * width, width, fields),
                ));
            }
        }
        let mut stores = c_skip();
        for (index, value) in values.into_iter().enumerate() {
            stores = c_seq(
                stores,
                c_typed_store(
                    c_add(target.clone(), c_uint64_literal(index as u64)),
                    value,
                    element,
                ),
            );
        }
        Ok(c_seq(captures, stores))
    }
}
