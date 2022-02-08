(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_36_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_36_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_36_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_g__8_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_4_function_g__8_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_3_1 Int))
(=> (and (and (nondet_interface_1_C_36_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_g__8_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 val_3_1))) (nondet_interface_1_C_36_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_5_function_f1__17_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_6_function_f1__17_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_1 Int))
(=> (and (and (nondet_interface_1_C_36_0 error_1 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_1 0) (summary_6_function_f1__17_36_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 state_2 val_11_1))) (nondet_interface_1_C_36_0 error_2 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |summary_7_function_a__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_8_function_a__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_1 Int))
(=> (and (and (nondet_interface_1_C_36_0 error_2 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_2 0) (summary_8_function_a__35_36_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_2))) (nondet_interface_1_C_36_0 error_3 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_9_function_g__8_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_10_g_7_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int))
(block_9_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int))
(=> (and (and (block_9_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_10_g_7_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1))))


(declare-fun |block_11_return_function_g__8_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_10_g_7_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1) (and (= val_3_2 44048180597813453602326562734351324025098966208897425494240603688123167145984) (and (= (select (|bytes_tuple_accessor_array| expr_5_length_pair_0) 2) 99) (and (= (select (|bytes_tuple_accessor_array| expr_5_length_pair_0) 1) 98) (and (= (select (|bytes_tuple_accessor_array| expr_5_length_pair_0) 0) 97) (and (= (|bytes_tuple_accessor_length| expr_5_length_pair_0) 3) (and (= val_3_1 0) true))))))) true) (block_11_return_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_2))))


(declare-fun |block_12_return_ghost_g_6_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_12_return_ghost_g_6_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_2) (and (= val_3_2 44048180597813453602326562734351324025098966208897425494240603688123167145984) (and (= (select (|bytes_tuple_accessor_array| expr_5_length_pair_0) 2) 99) (and (= (select (|bytes_tuple_accessor_array| expr_5_length_pair_0) 1) 98) (and (= (select (|bytes_tuple_accessor_array| expr_5_length_pair_0) 0) 97) (and (= (|bytes_tuple_accessor_length| expr_5_length_pair_0) 3) (and (= val_3_1 0) true))))))) true) (block_11_return_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_11_return_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1) true) true) (summary_3_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1))))


(declare-fun |block_13_function_g__8_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(block_13_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_13_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1) (and (summary_3_function_g__8_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 val_3_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_4_function_g__8_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 val_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_g__8_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_1) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_14_function_f1__17_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |block_15_f1_16_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(block_14_function_f1__17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_14_function_f1__17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_15_f1_16_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1))))


(declare-fun |block_16_return_function_f1__17_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(declare-fun |summary_17_function_g__8_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (summary_3_function_g__8_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_2) (summary_17_function_g__8_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_15_f1_16_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1) (and (summary_17_function_g__8_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_3_2) (and true (and (= val_11_1 0) true)))) (> error_1 0)) (summary_5_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_15_f1_16_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1) (and (= val_11_2 expr_14_0) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 val_3_2) (and (= error_1 0) (and (summary_17_function_g__8_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_3_2) (and true (and (= val_11_1 0) true)))))))) true) (block_16_return_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_2))))


(declare-fun |block_18_return_ghost_f1_15_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_18_return_ghost_f1_15_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_2) (and (= val_11_2 expr_14_0) (and (=> true (and (>= expr_14_0 0) (<= expr_14_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_14_0 val_3_2) (and (= error_1 0) (and (summary_17_function_g__8_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_3_2) (and true (and (= val_11_1 0) true)))))))) true) (block_16_return_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_16_return_function_f1__17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1) true) true) (summary_5_function_f1__17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1))))


(declare-fun |block_19_function_f1__17_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(block_19_function_f1__17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_19_function_f1__17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1) (and (summary_5_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3 val_11_1) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_1_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_1_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_1_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_1_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 3263152901)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 194)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 127)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 195)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 5)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_6_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3 val_11_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_6_function_f1__17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_1) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |block_20_function_a__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |block_21_a_34_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(block_20_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_20_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true)) true) (block_21_a_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_22_return_function_a__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_23_function_f1__17_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (summary_5_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_2) (summary_23_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_21_a_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_23_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_11_2) true)) (> error_1 0)) (summary_7_function_a__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_24_function_a__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_21_a_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_24_1 (= expr_22_0 44048180597813453602326562734351324025098966208897425494240603688123167145984)) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 2) 99) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 1) 98) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 0) 97) (and (= (|bytes_tuple_accessor_length| expr_23_length_pair_0) 3) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 val_11_2) (and (= error_1 0) (and (summary_23_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_11_2) true)))))))))) (and (not expr_24_1) (= error_2 2))) (block_24_function_a__35_36_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (block_24_function_a__35_36_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_7_function_a__35_36_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |summary_25_function_f1__17_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (summary_5_function_f1__17_36_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_3) (summary_25_function_f1__17_36_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1 val_11_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_21_a_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_25_function_f1__17_36_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_11_3) (and (= error_2 error_1) (and (= expr_24_1 (= expr_22_0 44048180597813453602326562734351324025098966208897425494240603688123167145984)) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 2) 99) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 1) 98) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 0) 97) (and (= (|bytes_tuple_accessor_length| expr_23_length_pair_0) 3) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 val_11_2) (and (= error_1 0) (and (summary_23_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_11_2) true)))))))))))) (> error_3 0)) (summary_7_function_a__35_36_0 error_3 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_26_function_a__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_21_a_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= expr_31_1 (= expr_29_0 44956353792602236728859952519244908696285197834109437979488219600636021309440)) (and (= (select (|bytes_tuple_accessor_array| expr_30_length_pair_0) 2) 101) (and (= (select (|bytes_tuple_accessor_array| expr_30_length_pair_0) 1) 100) (and (= (select (|bytes_tuple_accessor_array| expr_30_length_pair_0) 0) 99) (and (= (|bytes_tuple_accessor_length| expr_30_length_pair_0) 3) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 val_11_3) (and (= error_3 0) (and (summary_25_function_f1__17_36_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_11_3) (and (= error_2 error_1) (and (= expr_24_1 (= expr_22_0 44048180597813453602326562734351324025098966208897425494240603688123167145984)) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 2) 99) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 1) 98) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 0) 97) (and (= (|bytes_tuple_accessor_length| expr_23_length_pair_0) 3) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 val_11_2) (and (= error_1 0) (and (summary_23_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_11_2) true)))))))))))))))))))) (and (not expr_31_1) (= error_4 3))) (block_26_function_a__35_36_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (block_26_function_a__35_36_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (summary_7_function_a__35_36_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_21_a_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_4 error_3) (and (= expr_31_1 (= expr_29_0 44956353792602236728859952519244908696285197834109437979488219600636021309440)) (and (= (select (|bytes_tuple_accessor_array| expr_30_length_pair_0) 2) 101) (and (= (select (|bytes_tuple_accessor_array| expr_30_length_pair_0) 1) 100) (and (= (select (|bytes_tuple_accessor_array| expr_30_length_pair_0) 0) 99) (and (= (|bytes_tuple_accessor_length| expr_30_length_pair_0) 3) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_0 val_11_3) (and (= error_3 0) (and (summary_25_function_f1__17_36_0 error_3 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_11_3) (and (= error_2 error_1) (and (= expr_24_1 (= expr_22_0 44048180597813453602326562734351324025098966208897425494240603688123167145984)) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 2) 99) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 1) 98) (and (= (select (|bytes_tuple_accessor_array| expr_23_length_pair_0) 0) 97) (and (= (|bytes_tuple_accessor_length| expr_23_length_pair_0) 3) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_22_0 val_11_2) (and (= error_1 0) (and (summary_23_function_f1__17_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_1 val_11_2) true))))))))))))))))))))) true) (block_22_return_function_a__35_36_0 error_4 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_22_return_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (summary_7_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |block_27_function_a__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(block_27_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (block_27_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (summary_7_function_a__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 state_3) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_4_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_4_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_4_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_4_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 230582047)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 13)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 190)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 103)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 31)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) true))))))) true) (summary_8_function_a__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_8_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_28_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_29_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_29_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_30_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (contract_initializer_entry_29_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_30_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (contract_initializer_after_init_30_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_28_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_31_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_31_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (implicit_constructor_entry_31_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_28_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (implicit_constructor_entry_31_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_28_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int))
(=> (and (and (summary_constructor_2_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_11_4 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int) (val_3_3 Int))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_8_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 2))) error_target_5_0)))


(declare-fun |error_target_6_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_11_4 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int) (val_3_3 Int))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_8_function_a__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (= error_0 3))) error_target_6_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (error_3 Int) (error_4 Int) (expr_14_0 Int) (expr_22_0 Int) (expr_23_length_pair_0 |bytes_tuple|) (expr_24_1 Bool) (expr_29_0 Int) (expr_30_length_pair_0 |bytes_tuple|) (expr_31_1 Bool) (expr_5_length_pair_0 |bytes_tuple|) (funds_0_0 Int) (funds_1_0 Int) (funds_4_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (t_function_internal_pure$__$returns$_t_bytes32_$_abstract_0 Int) (this_0 Int) (tx_0 |tx_type|) (val_11_0 Int) (val_11_1 Int) (val_11_2 Int) (val_11_3 Int) (val_11_4 Int) (val_3_0 Int) (val_3_1 Int) (val_3_2 Int) (val_3_3 Int))
(=> error_target_6_0 false)))
(check-sat)