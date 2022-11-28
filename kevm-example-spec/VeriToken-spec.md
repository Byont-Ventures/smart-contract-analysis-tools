# VeriToken verification

```k
requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
```

## Generating and running the specifications

---

This template is based on the example specification from the demo repository [smart-contract-analysis-tools-example](https://github.com/Byont-Ventures/smart-contract-analysis-tools-example).

File [VeriToken.sol](../smart-contracts/src/VeriToken.sol) contains the solidity code being verified.

## Verification module

---

```k
requires "../security-scans/kevm/generated/VeriToken-bin-runtime.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports EVM-OPTIMIZATIONS
    imports VeriToken-VERIFICATION

    syntax Step ::= ByteArray | Int
    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

 // decimals lemmas
 // ---------------

    rule         255 &Int X <Int 256 => true requires 0 <=Int X [simplification, smt-lemma]
    rule 0 <=Int 255 &Int X          => true requires 0 <=Int X [simplification, smt-lemma]

endmodule
```

## K specification

---

```k
module VERITOKEN-SPEC
    imports VERIFICATION
```

### Functional claims

```k
claim <k> runLemma(#bufStrict(32, #loc(VeriToken._allowances[OWNER]))) => doneLemma(#buf(32, keccak(#buf(32, OWNER) ++ #buf(32, 1)))) ... </k>
      requires #rangeAddress(OWNER)
```

### Calling decimals() works

```k
claim [decimals]:
    <mode>     NORMAL   </mode>
    <schedule> ISTANBUL </schedule>

    <callStack> .List                                          </callStack>
    <program>   #binRuntime(VeriToken)                         </program>
    <jumpDests> #computeValidJumpDests(#binRuntime(VeriToken)) </jumpDests>

    <id>         ACCTID      => ?_ </id>
    <localMem>   .Memory     => ?_ </localMem>
    <memoryUsed> 0           => ?_ </memoryUsed>
    <wordStack>  .WordStack  => ?_ </wordStack>
    <pc>         0           => ?_ </pc>
    <endPC>      _           => ?_ </endPC>
    <gas>        #gas(_VGAS) => ?_ </gas>
    <callValue>  0           => ?_ </callValue>

    <callData>   VeriToken.decimals()       </callData>
    <k>          #execute   => #halt ...    </k>
    <output>     .ByteArray => #buf(32, 6)  </output>
    <statusCode> _          => EVMC_SUCCESS </statusCode>

    <account>
        <acctID> ACCTID </acctID>
        ...
    </account>
```

### Calling totalSupply() works

```k
claim [totalSupply]:
    <mode>     NORMAL   </mode>
    <schedule> ISTANBUL </schedule>

    <callStack> .List                                          </callStack>
    <program>   #binRuntime(VeriToken)                         </program>
    <jumpDests> #computeValidJumpDests(#binRuntime(VeriToken)) </jumpDests>

    <id>         ACCTID      => ?_ </id>
    <localMem>   .Memory     => ?_ </localMem>
    <memoryUsed> 0           => ?_ </memoryUsed>
    <wordStack>  .WordStack  => ?_ </wordStack>
    <pc>         0           => ?_ </pc>
    <endPC>      _           => ?_ </endPC>
    <gas>        #gas(_VGAS) => ?_ </gas>
    <callValue>  0           => ?_ </callValue>

    <callData>   VeriToken.totalSupply()             </callData>
    <k>          #execute   => #halt ...             </k>
    <output>     .ByteArray => #buf(32, TOTALSUPPLY) </output>
    <statusCode> _          => EVMC_SUCCESS          </statusCode>

    <account>
        <acctID> ACCTID </acctID>
        <storage> ACCT_STORAGE </storage>
        ...
     </account>

    requires TOTALSUPPLY_KEY ==Int #loc(VeriToken._totalSupply)
        andBool TOTALSUPPLY  ==Int #lookup(ACCT_STORAGE, TOTALSUPPLY_KEY)
```

### Calling approve(address spender, uint256 amount) works

```k
claim [approve.success]:
    <mode>     NORMAL   </mode>
    <schedule> ISTANBUL </schedule>

    <callStack> .List                                          </callStack>
    <program>   #binRuntime(VeriToken)                         </program>
    <jumpDests> #computeValidJumpDests(#binRuntime(VeriToken)) </jumpDests>
    <static>    false                                          </static>

    <id>         ACCTID      => ?_ </id>
    <caller>     OWNER       => ?_ </caller>
    <localMem>   .Memory     => ?_ </localMem>
    <memoryUsed> 0           => ?_ </memoryUsed>
    <wordStack>  .WordStack  => ?_ </wordStack>
    <pc>         0           => ?_ </pc>
    <endPC>      _           => ?_ </endPC>
    <gas>        #gas(_VGAS) => ?_ </gas>
    <callValue>  0           => ?_ </callValue>
    <substate> _             => ?_ </substate>

    <callData>   VeriToken.approve(SPENDER, AMOUNT) </callData>
    <k>          #execute   => #halt ...            </k>
    <output>     .ByteArray => #buf(32, 1)          </output>
    <statusCode> _          => EVMC_SUCCESS         </statusCode>

    <account>
        <acctID> ACCTID </acctID>
        <storage> ACCT_STORAGE => ACCT_STORAGE [ ALLOWANCE_KEY <- AMOUNT ] </storage>
        ...
    </account>

    requires ALLOWANCE_KEY ==Int #loc(VeriToken._allowances[OWNER][SPENDER])
        andBool #rangeAddress(OWNER)
        andBool #rangeAddress(SPENDER)
        andBool #rangeUInt(256, AMOUNT)
        andBool OWNER =/=Int 0
        andBool SPENDER =/=Int 0
```

```k
claim [approve.revert]:
    <mode>     NORMAL   </mode>
    <schedule> ISTANBUL </schedule>

    <callStack> .List                                      </callStack>
    <program>   #binRuntime(VeriToken)                         </program>
    <jumpDests> #computeValidJumpDests(#binRuntime(VeriToken)) </jumpDests>
    <static>    false                                      </static>

    <id>         ACCTID      => ?_ </id>
    <caller>     OWNER       => ?_ </caller>
    <localMem>   .Memory     => ?_ </localMem>
    <memoryUsed> 0           => ?_ </memoryUsed>
    <wordStack>  .WordStack  => ?_ </wordStack>
    <pc>         0           => ?_ </pc>
    <endPC>      _           => ?_ </endPC>
    <gas>        #gas(_VGAS) => ?_ </gas>
    <callValue>  0           => ?_ </callValue>
    <substate> _             => ?_ </substate>

    <callData>   VeriToken.approve(SPENDER, AMOUNT) </callData>
    <k>          #execute   => #halt ...            </k>
    <output>     _          => ?_                   </output>
    <statusCode> _          => EVMC_REVERT          </statusCode>

    <acctID> ACCTID </acctID>
        <account>
        <storage> _ACCT_STORAGE </storage>
        ...
    </account>

    requires #rangeAddress(OWNER)
        andBool #rangeAddress(SPENDER)
        andBool #rangeUInt(256, AMOUNT)
        andBool (OWNER ==Int 0 orBool SPENDER ==Int 0)
```

### Calling transfer(address to, uint256 amount) works

```k
claim [transfer.success]:
    <mode>     NORMAL   </mode>
    <schedule> ISTANBUL </schedule>

    <callStack> .List                                          </callStack>
    <program>   #binRuntime(VeriToken)                         </program>
    <jumpDests> #computeValidJumpDests(#binRuntime(VeriToken)) </jumpDests>
    <static>    false                                          </static>

    <id>         ACCTID      => ?_ </id>
    <caller>     OWNER       => ?_ </caller>
    <localMem>   .Memory     => ?_ </localMem>
    <memoryUsed> 0           => ?_ </memoryUsed>
    <wordStack>  .WordStack  => ?_ </wordStack>
    <pc>         0           => ?_ </pc>
    <endPC>      _           => ?_ </endPC>
    <gas>        #gas(_VGAS) => ?_ </gas>
    <callValue>  0           => ?_ </callValue>
    <substate>   _           => ?_ </substate>

    <callData>   VeriToken.transfer(RECEIVER, AMOUNT)    </callData>
    <k>          #execute   => #halt ...                 </k>
    <output>     .ByteArray => #buf(32, bool2Word(true)) </output>
    <statusCode> _          => EVMC_SUCCESS              </statusCode>

    <account>
        <acctID> ACCTID </acctID>
        <storage>
            BALANCE_OWNER_KEY    |-> (BALANCE_INITIAL_OWNER    => BALANCE_NEW_OWNER)
            BALANCE_RECEIVER_KEY |-> (BALANCE_INITIAL_RECEIVER => BALANCE_NEW_RECEIVER)
        </storage>
        <origStorage>
            BALANCE_OWNER_KEY    |-> BALANCE_INITIAL_OWNER
            BALANCE_RECEIVER_KEY |-> BALANCE_INITIAL_RECEIVER
        </origStorage>
        ...
    </account>

    requires
        BALANCE_OWNER_KEY ==Int #loc(VeriToken._balances[OWNER])
        andBool BALANCE_RECEIVER_KEY ==Int #loc(VeriToken._balances[RECEIVER])
        andBool #rangeAddress(OWNER)
        andBool #rangeAddress(RECEIVER)
        andBool OWNER =/=Int 0
        andBool RECEIVER =/=Int 0
        andBool OWNER =/=Int RECEIVER
        andBool #rangeUInt(256, BALANCE_INITIAL_OWNER)
        andBool #rangeUInt(256, BALANCE_INITIAL_RECEIVER)
        andBool AMOUNT >=Int 0
        andBool AMOUNT <=Int BALANCE_INITIAL_OWNER
        andBool BALANCE_NEW_OWNER ==Int (BALANCE_INITIAL_OWNER -Int AMOUNT)
        andBool BALANCE_NEW_RECEIVER ==Int (BALANCE_INITIAL_RECEIVER +Int AMOUNT)
        andBool #rangeUInt(256, BALANCE_NEW_OWNER)
        andBool #rangeUInt(256, BALANCE_NEW_RECEIVER)
```

```k
endmodule
```
