(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-datatypes ((|tuple()| 0)) (((|tuple()|))))
(declare-fun |interface_0_C_36_0| (Int |abi_type| |crypto_type| |state_type| Bool ) Bool)
(declare-fun |nondet_interface_1_C_36_0| (Int Int |abi_type| |crypto_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_constructor_2_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (lock_3_0 Bool) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_36_0 error_0 this_0 abi_0 crypto_0 state_0 lock_3_0 state_0 lock_3_0))))


(declare-fun |summary_3_function_f__18_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_4_function_f__18_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_36_0 error_0 this_0 abi_0 crypto_0 state_0 lock_3_0 state_1 lock_3_1) true) (and (= error_0 0) (summary_4_function_f__18_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 lock_3_1 state_2 lock_3_2))) (nondet_interface_1_C_36_0 error_1 this_0 abi_0 crypto_0 state_0 lock_3_0 state_2 lock_3_2))))


(declare-fun |summary_5_function_g__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_6_function_g__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_36_0 error_1 this_0 abi_0 crypto_0 state_0 lock_3_0 state_1 lock_3_1) true) (and (= error_1 0) (summary_6_function_g__35_36_0 error_2 this_0 abi_0 crypto_0 tx_0 state_1 lock_3_1 state_2 lock_3_2))) (nondet_interface_1_C_36_0 error_2 this_0 abi_0 crypto_0 state_0 lock_3_0 state_2 lock_3_2))))


(declare-fun |block_7_function_f__18_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |block_8_f_17_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_7_function_f__18_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_function_f__18_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= lock_3_1 lock_3_0))) true) true)) true) (block_8_f_17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1))))


(declare-fun |block_9_return_function_f__18_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_10_function_g__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (summary_5_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_2 lock_3_3) (summary_10_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_2 lock_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_f_17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (and (summary_10_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 lock_3_2 state_2 lock_3_3) (and (= lock_3_2 expr_8_1) (and (= expr_8_1 expr_7_0) (and (= expr_6_0 lock_3_1) (and (= expr_7_0 false) true)))))) (> error_1 0)) (summary_3_function_f__18_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_2 lock_3_3))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_8_f_17_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (and (= lock_3_4 expr_15_1) (and (= expr_15_1 expr_14_0) (and (= expr_13_0 lock_3_3) (and (= expr_14_0 true) (and (= error_1 0) (and (summary_10_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 lock_3_2 state_2 lock_3_3) (and (= lock_3_2 expr_8_1) (and (= expr_8_1 expr_7_0) (and (= expr_6_0 lock_3_1) (and (= expr_7_0 false) true))))))))))) true) (block_9_return_function_f__18_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_2 lock_3_4))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_return_function_f__18_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) true) true) (summary_3_function_f__18_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1))))


(declare-fun |block_11_function_f__18_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_11_function_f__18_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_11_function_f__18_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (and (summary_3_function_f__18_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 lock_3_1 state_3 lock_3_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_0_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_0_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_0_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_0_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 638722032)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 38)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 18)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 31)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 240)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= lock_3_1 lock_3_0))) true) true))))))) true) (summary_4_function_f__18_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_3 lock_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0 lock_3_0) true) (and (summary_4_function_f__18_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1 lock_3_1))))


(declare-fun |block_12_function_g__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |block_13_g_34_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_12_function_g__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_12_function_g__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= lock_3_1 lock_3_0))) true) true)) true) (block_13_g_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1))))


(declare-fun |block_14_return_function_g__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |block_15_function_g__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_g_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (and (= expr_31_1 (= expr_29_1 expr_30_0)) (and (=> true true) (and (= expr_30_0 0) (and (=> true (and (>= expr_29_1 0) (<= expr_29_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_1 (|msg.value| tx_0)) (and (=> true expr_24_1) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (= expr_23_0 false) (and (= expr_22_0 lock_3_1) true)))))))))) (and (not expr_31_1) (= error_1 1))) (block_15_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_15_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (summary_5_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_13_g_34_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (and (= error_1 error_0) (and (= expr_31_1 (= expr_29_1 expr_30_0)) (and (=> true true) (and (= expr_30_0 0) (and (=> true (and (>= expr_29_1 0) (<= expr_29_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_29_1 (|msg.value| tx_0)) (and (=> true expr_24_1) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (= expr_23_0 false) (and (= expr_22_0 lock_3_1) true))))))))))) true) (block_14_return_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_14_return_function_g__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) true) true) (summary_5_function_g__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1))))


(declare-fun |block_16_function_g__35_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_16_function_g__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_16_function_g__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (and (summary_5_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 lock_3_1 state_3 lock_3_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and true (= (|msg.sig| tx_0) 3793197966)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 226)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 23)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 155)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 142)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= lock_3_1 lock_3_0))) true) true))))))) true) (summary_6_function_g__35_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_3 lock_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0 lock_3_0) true) (and (summary_6_function_g__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1 lock_3_1))))


(declare-fun |contract_initializer_17_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(declare-fun |contract_initializer_entry_18_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= lock_3_1 lock_3_0))) (contract_initializer_entry_18_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_1))))


(declare-fun |contract_initializer_after_init_19_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_18_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_1) (and (= lock_3_2 expr_2_0) (and (= expr_2_0 true) true))) true) (contract_initializer_after_init_19_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_19_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_1) true) true) (contract_initializer_17_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_1))))


(declare-fun |implicit_constructor_entry_20_C_36_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Bool Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= lock_3_1 lock_3_0))) (and true (= lock_3_1 false))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_20_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_1))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_20_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_1) (and (contract_initializer_17_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 lock_3_1 lock_3_2) true)) (> error_1 0)) (summary_constructor_2_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 lock_3_0 lock_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_20_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_1) (and (= error_1 0) (and (contract_initializer_17_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 lock_3_1 lock_3_2) true))) true) (summary_constructor_2_C_36_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 lock_3_0 lock_3_2))))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 lock_3_0 lock_3_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_36_0 this_0 abi_0 crypto_0 state_1 lock_3_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0 lock_3_0) true) (and (summary_4_function_f__18_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_36_0 this_0 abi_0 crypto_0 state_0 lock_3_0) true) (and (summary_6_function_g__35_36_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 lock_3_0 state_1 lock_3_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_11_1 |tuple()|) (expr_13_0 Bool) (expr_14_0 Bool) (expr_15_1 Bool) (expr_22_0 Bool) (expr_23_0 Bool) (expr_24_1 Bool) (expr_29_1 Int) (expr_2_0 Bool) (expr_30_0 Int) (expr_31_1 Bool) (expr_6_0 Bool) (expr_7_0 Bool) (expr_8_1 Bool) (funds_0_0 Int) (funds_2_0 Int) (lock_3_0 Bool) (lock_3_1 Bool) (lock_3_2 Bool) (lock_3_3 Bool) (lock_3_4 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_3_0 false)))
(check-sat)