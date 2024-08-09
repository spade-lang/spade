pub mod id_tracker;
pub mod location_info;
pub mod name;
pub mod namespace;
pub mod num_ext;

use itertools::Itertools;

pub fn pluralize<'s>(len: usize, singular: &'s str, plural: &'s str) -> &'s str {
    if len == 1 {
        singular
    } else {
        plural
    }
}

pub fn format_list(strings: &[impl AsRef<str>]) -> String {
    if strings.len() == 0 {
        String::new()
    } else if strings.len() == 1 {
        strings[0].as_ref().to_string()
    } else {
        format!(
            "{} and {}",
            strings
                .get(0..strings.len() - 1)
                .unwrap()
                .into_iter()
                .map(AsRef::as_ref)
                .join(", "),
            strings.last().unwrap().as_ref(),
        )
    }
}
