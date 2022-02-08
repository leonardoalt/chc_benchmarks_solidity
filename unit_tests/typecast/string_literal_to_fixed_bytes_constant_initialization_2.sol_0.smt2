(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_MockContract_14_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_MockContract_14_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_MockContract_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_MockContract_14_0 error_0 this_0 abi_0 crypto_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_0 SENTINEL_ANY_MOCKS_3_0))))


(declare-fun |summary_3_constructor_13_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_4_constructor_13_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_5__12_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_4_constructor_13_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1)))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_4_constructor_13_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= SENTINEL_ANY_MOCKS_3_1 SENTINEL_ANY_MOCKS_3_0))) true) true)) true) (block_5__12_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1))))


(declare-fun |block_6_return_constructor_13_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |block_7_constructor_13_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5__12_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (and (= expr_9_1 (>= expr_7_0 expr_8_0)) (and (=> true true) (and (= expr_8_0 0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 4294967295))) (and (= expr_7_0 16777216) (and (= (select (|bytes_tuple_accessor_array| expr_2_length_pair_0) 0) 1) (and (= (|bytes_tuple_accessor_length| expr_2_length_pair_0) 1) true)))))))) (and (not expr_9_1) (= error_1 1))) (block_7_constructor_13_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1))))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_7_constructor_13_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (summary_3_constructor_13_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1))))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5__12_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (and (= error_1 error_0) (and (= expr_9_1 (>= expr_7_0 expr_8_0)) (and (=> true true) (and (= expr_8_0 0) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 4294967295))) (and (= expr_7_0 16777216) (and (= (select (|bytes_tuple_accessor_array| expr_2_length_pair_0) 0) 1) (and (= (|bytes_tuple_accessor_length| expr_2_length_pair_0) 1) true))))))))) true) (block_6_return_constructor_13_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1))))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_return_constructor_13_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) true) true) (summary_3_constructor_13_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1))))


(declare-fun |contract_initializer_8_MockContract_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |contract_initializer_entry_9_MockContract_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= SENTINEL_ANY_MOCKS_3_1 SENTINEL_ANY_MOCKS_3_0))) true) (contract_initializer_entry_9_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1))))


(declare-fun |contract_initializer_after_init_10_MockContract_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_9_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (and (= SENTINEL_ANY_MOCKS_3_2 16777216) (and (= (select (|bytes_tuple_accessor_array| expr_2_length_pair_1) 0) 1) (and (= (|bytes_tuple_accessor_length| expr_2_length_pair_1) 1) true)))) true) (contract_initializer_after_init_10_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_2))))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_10_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (and (summary_3_constructor_13_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 SENTINEL_ANY_MOCKS_3_1 state_2 SENTINEL_ANY_MOCKS_3_2) true)) (> error_1 0)) (contract_initializer_8_MockContract_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_2 SENTINEL_ANY_MOCKS_3_2))))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_10_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (and (= error_1 0) (and (summary_3_constructor_13_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 SENTINEL_ANY_MOCKS_3_1 state_2 SENTINEL_ANY_MOCKS_3_2) true))) true) (contract_initializer_8_MockContract_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_2 SENTINEL_ANY_MOCKS_3_2))))


(declare-fun |implicit_constructor_entry_11_MockContract_14_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int |state_type| Int ) Bool)
(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (and (= state_2 state_0) (= error_1 0)) (and true (= SENTINEL_ANY_MOCKS_3_2 SENTINEL_ANY_MOCKS_3_0))) true) (and true (= SENTINEL_ANY_MOCKS_3_2 0))) (>= (select (|balances| state_2) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_11_MockContract_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_2 SENTINEL_ANY_MOCKS_3_2))))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_11_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (and (contract_initializer_8_MockContract_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 SENTINEL_ANY_MOCKS_3_1 state_2 SENTINEL_ANY_MOCKS_3_2) true)) (> error_1 0)) (summary_constructor_2_MockContract_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_2 SENTINEL_ANY_MOCKS_3_2))))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_11_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) (and (= error_1 0) (and (contract_initializer_8_MockContract_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 SENTINEL_ANY_MOCKS_3_1 state_2 SENTINEL_ANY_MOCKS_3_2) true))) true) (summary_constructor_2_MockContract_14_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_2 SENTINEL_ANY_MOCKS_3_2))))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_MockContract_14_0 this_0 abi_0 crypto_0 state_1 SENTINEL_ANY_MOCKS_3_1))))


(declare-fun |error_target_2_0| () Bool)
(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_MockContract_14_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 SENTINEL_ANY_MOCKS_3_0 state_1 SENTINEL_ANY_MOCKS_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_2_0)))


(assert
(forall ( (SENTINEL_ANY_MOCKS_3_0 Int) (SENTINEL_ANY_MOCKS_3_1 Int) (SENTINEL_ANY_MOCKS_3_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_length_pair_0 |bytes_tuple|) (expr_2_length_pair_1 |bytes_tuple|) (expr_7_0 Int) (expr_8_0 Int) (expr_9_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_2_0 false)))
(check-sat)