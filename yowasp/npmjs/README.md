YoWASP Spade package
====================

This package provides [Spade][] binaries built for [WebAssembly][]. This is using the yowasp project to do the heavy lifting. See the [overview of the YoWASP project][yowasp] for details.

At the moment, this package only provides an API allowing to run Spade in a virtual filesystem; no binaries are provided.

[Spade]: https://gitlab.com/spade-lang/spade/
[webassembly]: https://webassembly.org/
[yowasp]: https://yowasp.github.io/


API reference
-------------

This package provides one function:

- `runSpade`

For more detail, see the documentation for [the JavaScript YoWASP runtime](https://github.com/YoWASP/runtime-js#api-reference).


Versioning
----------

The version of this package is derived from the upstream Spade package version. The format is `X.Y.Z-dev-N1.N2.H1-H2` format

1. `X`: Spade major version
2. `Y`: Spade minor version
3. `Z`: Spade patch version
4. `N1`: The number of commits in the Spade repo when this was built
4. `N2`: The number of commits in this repo when this was built
3. `H1`: The commit hash which Spade was built from
4. `H2`: The commit hash of this repo

With this scheme, there is a direct correspondence between upstream versions and [SemVer][semver] NPM package versions.

Note that for development builds, the minor version is incremented as required by the SemVer comparison order. This means that an NPM package built from the upstream version `0.45+12` and the 120th commit in this repository will have the version `0.46.12-dev.120`. Because this is a pre-release package, it will not be matched by version specifiers such as `^0.46` or `>=0.46`.

[semver]: https://semver.org/

Credit
------

All of the heavy lifting here is done by  Catherine "whitequark" via the https://github.com/YoWASP project.


License
-------

This package and the Spade compiler is covered by the [EUPL-1.2](LICENSE.txt). The Spade standard library is dual licensed under the Apache and MIT licenses. The YoWASP build flow used to bundle Spade in JavaScript is originally licensed under the [ISC](LICENSE-ISC-whitequark.txt)
