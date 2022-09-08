## Some notes about the `randombit` example

### `src`

```
jasmin-zk/src/examples/randombit$ make
```

produces `randombit.s`.

```
jasmin-zk/src/examples/randombit$ make extract
```

produces `jasmin-zk/proof/examples/randombit/{Array1.ec, randombit_s.ec, WArray1.ec}`.

### `proof`

```
jasmin-zk/proof/examples/randombit$ easycrypt randombit_s.ec
```

produces
```
[critical] [randombit_s.ec: line 18 (14-30)] unknown function: SC.randombytes_1
[|] [0024] 99.8 % (-1.0B / [frag -1.0B])
```
as expected, since there is no definition for `randombytes`. Contributions are welcome.


### `test`
```
jasmin-zk/test/examples/randombit$ make
```

produces two binaries: `randombit0` and `randombit1`. I only pushed two test examples to check if the Makefiles work.

```
jasmin-zk/test/examples/randombit$ make run
```

Runs all binaries.

