use std::sync::atomic::{AtomicUsize, Ordering};

use melior::ir::{operation::OperationLike, BlockLike, BlockRef, OperationRef};

pub(crate) static FRESH_WAVELET_NAMES: FreshWaveletNames = FreshWaveletNames::new();

pub(crate) struct FreshWaveletNames {
    counter: AtomicUsize,
}

impl FreshWaveletNames {
    pub(crate) const fn new() -> Self {
        Self {
            counter: AtomicUsize::new(0),
        }
    }

    pub(crate) fn fresh(&self, prefix: &str) -> String {
        let mut sanitized = String::with_capacity(prefix.len() + 16);
        for character in prefix.chars() {
            if character.is_ascii_alphanumeric() || character == '_' {
                sanitized.push(character);
            } else {
                sanitized.push('_');
            }
        }

        let has_valid_start = sanitized
            .as_bytes()
            .first()
            .is_some_and(|character| character.is_ascii_alphabetic() || *character == b'_');
        if sanitized.is_empty() {
            sanitized.push('v');
        } else if !has_valid_start {
            sanitized.insert_str(0, "v_");
        }

        let number = self
            .counter
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |number| {
                number.checked_add(1)
            })
            .expect("fresh Wavelet name counter overflowed");
        format!("{sanitized}{number}")
    }
}

pub(crate) fn fresh_wavelet_name(prefix: &str) -> String {
    FRESH_WAVELET_NAMES.fresh(prefix)
}

pub(crate) struct BlockIter<'c, 'a> {
    next: Option<OperationRef<'c, 'a>>,
}

impl<'c, 'a> BlockIter<'c, 'a> {
    pub(crate) fn new(block: BlockRef<'c, 'a>) -> Self {
        Self {
            next: block.first_operation(),
        }
    }

    pub(crate) fn from_operation(operation: OperationRef<'c, 'a>) -> Self {
        Self {
            next: Some(operation),
        }
    }
}

impl<'c, 'a> From<BlockRef<'c, 'a>> for BlockIter<'c, 'a> {
    fn from(block: BlockRef<'c, 'a>) -> Self {
        Self::new(block)
    }
}

impl<'c, 'a> From<OperationRef<'c, 'a>> for BlockIter<'c, 'a> {
    fn from(operation: OperationRef<'c, 'a>) -> Self {
        Self::from_operation(operation)
    }
}

impl<'c, 'a> Iterator for BlockIter<'c, 'a> {
    type Item = OperationRef<'c, 'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let operation = self.next.take()?;
        self.next = operation.next_in_block();
        Some(operation)
    }
}

#[cfg(test)]
mod tests {
    use super::{fresh_wavelet_name, FreshWaveletNames};

    #[test]
    fn fresh_wavelet_names_are_unique_and_valid_identifiers() {
        static NAMES: FreshWaveletNames = FreshWaveletNames::new();

        assert_eq!(NAMES.fresh("value"), "value0");
        assert_eq!(NAMES.fresh("value"), "value1");
        assert_eq!(NAMES.fresh("9 bad-name.$"), "v_9_bad_name__2");
        assert_eq!(NAMES.fresh(""), "v3");

        assert_ne!(
            fresh_wavelet_name("temporary"),
            fresh_wavelet_name("temporary")
        );
    }
}
