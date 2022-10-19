## how do we test/benchmark this?

make sure your GOPATH and PATH are set.  install benchstat (if you want pretty
benchmarks with standard deviation etc)

To run tests:

```
go test
```

with benchmarks too:

```
go test -bench=.
```

If you want to run some but not
all benchmarks, use either the benchmark function's name in place of the `.` or
some regex that will capture all the benchmarks you want to run.

To run benchmarks without tests:

```
go test -run=^$ -bench=.
```

`-run=^$` excludes all tests in the test suite. To get better stats, run them
multiple times, saving into a file so we can apply benchstat later.

```
go test -count=20 -run=^$ -bench=. | tee -a master-benchmark
```

This'll
print to stdout and master-benchmark. Then run benchstat on the file produced:

```
benchstat master-benchmark
```
