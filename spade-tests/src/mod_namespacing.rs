use crate::snapshot_error;
use spade_common::name::Path;

snapshot_error! {
    missing_mod_for_file,
    {
        {
            Path::from_strs(&["proj"]),
            Path::from_strs(&["proj"]),
            "src/main.spade",
            "fn just_some_stuff() {}"
        },
        {
            Path::from_strs(&["proj", "subfile"]),
            Path::from_strs(&["proj"]),
            "src/subfile.spade",
            ""
        }
    },
    false
}

snapshot_error! {
    missing_mod_for_directory,
    {
        {
            Path::from_strs(&["proj"]),
            Path::from_strs(&["proj"]),
            "src/main.spade",
            "fn just_some_stuff() {}"
        },
        {
            Path::from_strs(&["proj", "submod"]),
            Path::from_strs(&["proj"]),
            "src/submod/mod.spade",
            ""
        }
    },
    false
}

snapshot_error! {
    missing_mod_for_subfile_in_subdir,
    {
        {
            Path::from_strs(&["proj"]),
            Path::from_strs(&["proj"]),
            "src/main.spade",
            "mod submod;"
        },
        {
            Path::from_strs(&["proj", "submod"]),
            Path::from_strs(&["proj"]),
            "src/submod/main.spade",
            ""
        },
        {
            Path::from_strs(&["proj", "submod", "subfile"]),
            Path::from_strs(&["proj", "submod"]),
            "src/submod/subfile.spade",
            ""
        }
    },
    false
}

snapshot_error! {
    mod_but_no_file,
    {
        {
            Path::from_strs(&["proj"]),
            Path::from_strs(&["proj"]),
            "src/main.spade",
            "mod submod;
            "
        },
        {
            Path::from_strs(&["proj", "submod"]),
            Path::from_strs(&["proj"]),
            "src/submod/main.spade",
            "mod subsubmod;
            "
        }
    },
    false
}

snapshot_error! {
    missing_mod_in_external_lib,
    {
        {
            Path::from_strs(&["proj"]),
            Path::from_strs(&["proj"]),
            "src/main.spade",
            "mod submod;
            "
        },
        {
            Path::from_strs(&["dep"]),
            Path::from_strs(&["dep"]),
            "build/test/src/main.spade",
            "mod submod;
            "
        },
    },
    false
}
