(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_9_0| (Int |abi_type| |crypto_type| |state_type| Int Int ) Bool)
(declare-fun |nondet_interface_1_C_9_0| (Int Int |abi_type| |crypto_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_constructor_2_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (z_3_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_9_0 error_0 this_0 abi_0 crypto_0 state_0 z_3_0 x_8_0 state_0 z_3_0 x_8_0))))


(declare-fun |contract_initializer_3_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(declare-fun |contract_initializer_entry_4_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (z_3_0 Int) (z_3_1 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_3_0 z_3_0)) (= x_8_0 x_8_0))) (contract_initializer_entry_4_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_0 x_8_0))))


(declare-fun |local_error_5_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (and (and (contract_initializer_entry_4_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 z_3_2) (and (=> true true) (and (= expr_5_0 2) (and (= z_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 0) true)))))))) (and (= expr_6_0 0) (= error_1 1))) (local_error_5_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_2 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (local_error_5_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_2 x_8_1) (contract_initializer_3_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_2 x_8_1))))


(declare-fun |contract_initializer_after_init_6_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (and (and (contract_initializer_entry_4_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1) (and (= x_8_2 expr_7_1) (and (=> true (and (>= expr_7_1 0) (<= expr_7_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_7_1 (div expr_5_0 expr_6_0)) (and (= error_1 error_0) (and (=> true (and (>= expr_6_0 0) (<= expr_6_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_6_0 z_3_2) (and (=> true true) (and (= expr_5_0 2) (and (= z_3_2 expr_2_0) (and (=> true true) (and (= expr_2_0 0) true)))))))))))) true) (contract_initializer_after_init_6_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_2 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (and (and (contract_initializer_after_init_6_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1) true) true) (contract_initializer_3_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1))))


(declare-fun |implicit_constructor_entry_7_C_9_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and (and true (= z_3_1 z_3_0)) (= x_8_1 x_8_0))) (and (and true (= z_3_1 0)) (= x_8_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_7_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (and (and (implicit_constructor_entry_7_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1) (and (contract_initializer_3_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 z_3_1 x_8_1 z_3_2 x_8_2) true)) (> error_1 0)) (summary_constructor_2_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 z_3_0 x_8_0 z_3_2 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (and (and (implicit_constructor_entry_7_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1) (and (= error_1 0) (and (contract_initializer_3_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 z_3_1 x_8_1 z_3_2 x_8_2) true))) true) (summary_constructor_2_C_9_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 z_3_0 x_8_0 z_3_2 x_8_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (and (and (summary_constructor_2_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_9_0 this_0 abi_0 crypto_0 state_1 z_3_1 x_8_1))))


(declare-fun |error_target_2_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> (and (and (summary_constructor_2_C_9_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 z_3_0 x_8_0 z_3_1 x_8_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 1))) error_target_2_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_2_0 Int) (expr_5_0 Int) (expr_6_0 Int) (expr_7_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_8_0 Int) (x_8_1 Int) (x_8_2 Int) (z_3_0 Int) (z_3_1 Int) (z_3_2 Int))
(=> error_target_2_0 false)))
(check-sat)