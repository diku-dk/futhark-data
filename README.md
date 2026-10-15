# Futhark implementation of the Futhark binary data format

This library provides a Futhark implementation of the [Futhark binary data
format](https://futhark.readthedocs.io/en/latest/binary-data-format.html). It is
intended for light preprocessing of data files used for benchmarking and
testing, particularly in conjunction with the `io.loadbytes` IO function. For
nontrivial management of data files it is better to use an implementation in a
general-purpose language.
