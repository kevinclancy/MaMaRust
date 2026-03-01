use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_STAMP: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Debug)]
pub struct Ident {
    pub name: String,
    stamp: u64,
}

impl Ident {
    pub fn new(name: String) -> Ident {
        let stamp = NEXT_STAMP.fetch_add(1, Ordering::Relaxed);
        Ident { name, stamp }
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.stamp == other.stamp
    }
}

impl Eq for Ident {}

impl Hash for Ident {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.stamp.hash(state);
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}
