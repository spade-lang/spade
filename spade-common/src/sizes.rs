use itertools::Itertools;
use postcard::experimental::serialized_size;
use rustc_hash::FxHashMap as HashMap;
use serde::Serialize;

pub trait SerializedSize: Serialize {
    fn accumulate_size(&self, field: &[&'static str], into: &mut HashMap<Vec<&'static str>, usize>);

    fn report_size(&self) {
        let total_size = serialized_size(self).unwrap();
        let mut into = HashMap::default();
        self.accumulate_size(&[], &mut into);

        for (name, size) in into
            .iter()
            .sorted_by_key(|(k, _)| (k.len(), k.last().unwrap_or(&"")))
        {
            let ratio = ((*size as f32 / total_size as f32) * 100.).round();
            println!("{}: {} ({})", name.iter().join("."), size, ratio);
        }
    }
}

pub fn add_field<T: Serialize>(
    outer_path: &[&'static str],
    field_name: &'static str,
    t: &T,
    into: &mut HashMap<Vec<&'static str>, usize>,
) {
    let mut path = outer_path.to_vec();
    path.push(field_name);
    *into.entry(path).or_default() += postcard::experimental::serialized_size(t).unwrap();
}
