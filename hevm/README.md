# hevm

The hevm tool is a symbolic executor which is originally part of the [dapptools](https://github.com/dapphub/dapptools/tree/master/src/hevm) suite. In august 2022 is was [forked](https://github.com/ethereum/hevm) by the formal methods team at the Ethereum Foundation.

## Runnning

You might need to run `sudo` on the command below.

```bash
$ ./run-hevm.sh ${PWD}/../ VeriToken 'transfer(address, uint256)' 0.8.17
```

The output can then be found in [VeriToken-transfer-hevm.result](./VeriToken-transfer-hevm.result).

## Limitations

As of now, `hevm` is probably better used as part of the whole dapphub framework where the `prove` prefix for tests will make use of hevm. Then also the cheatcodes (as we know from `forge`) can be used.

Symbolic execution on storage is [not supported](https://github.com/dapphub/dapptools/tree/master/src/hevm#hevm-symbolic). In a blog post on [fv.ethereum.org](https://fv.ethereum.org/2020/07/28/symbolic-hevm-release/#limitations) it shows that (in 2020) hevm still had its limitations. It should be verified with the git repository which of these limitations are still relevant.

Using the option `--storage-model InitialS` is recommended and get's you going. But it is still not perfect.

Currently, hevm also gives an error when dealing with the `call` function in the `resignFromAuctoin()` function in VeriAuctionTokenForEth_problems

```Solidity
(bool transferSuccess, ) = msg.sender.call{value: commitment}("");
```

It gives the following error

```
hevm: unexpected symbolic argument
CallStack (from HasCallStack):
  error, called at src/EVM/Symbolic.hs:42:14 in hevm-0.48.1-KdjyJ1kXYK7IQeiBwTCoFo:EVM.Symbolic
```
