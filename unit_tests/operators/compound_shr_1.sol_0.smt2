(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_23_0| (Int |abi_type| |crypto_type| |state_type| ) Bool)
(declare-fun |nondet_interface_1_C_23_0| (Int Int |abi_type| |crypto_type| |state_type| |state_type| ) Bool)
(declare-fun |summary_constructor_2_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_23_0 error_0 this_0 abi_0 crypto_0 state_0 state_0))))


(declare-fun |summary_3_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(declare-fun |summary_4_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_23_0 error_0 this_0 abi_0 crypto_0 state_0 state_1) true) (and (= error_0 0) (summary_4_function_f__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 b_2_0 state_2 b_2_1))) (nondet_interface_1_C_23_0 error_1 this_0 abi_0 crypto_0 state_0 state_2))))


(declare-fun |block_5_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_6_f_21_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int))
(block_5_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int))
(=> (and (and (block_5_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= b_2_1 b_2_0))) true)) true) (block_6_f_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1))))


(declare-fun |block_7_return_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_8_if_header_f_14_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_9_if_true_f_13_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(declare-fun |block_10_f_21_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (block_6_f_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (and (= v_6_2 expr_7_0) (and (=> true true) (and (= expr_7_0 1) (and true (and (= v_6_1 0) true)))))) true) (block_8_if_header_f_14_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_9_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (block_8_if_header_f_14_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (and (= expr_9_0 b_2_1) true)) expr_9_0) (block_9_if_true_f_13_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_7_0 Int) (expr_9_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (block_8_if_header_f_14_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (and (= expr_9_0 b_2_1) true)) (not expr_9_0)) (block_10_f_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_7_0 Int) (expr_9_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (block_9_if_true_f_13_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (and (= v_6_2 expr_12_1) (and (=> true (and (>= expr_12_1 0) (<= expr_12_1 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_12_1 (bv2nat (bvlshr (ite (>= v_6_1 0) ((_ int2bv 256) v_6_1) (bvneg ((_ int2bv 256) (- v_6_1)))) (ite (>= expr_11_0 0) ((_ int2bv 256) expr_11_0) (bvneg ((_ int2bv 256) (- expr_11_0))))))) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_10_0 v_6_1) (and (=> true true) (and (= expr_11_0 2) true)))))))) true) (block_10_f_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_2))))


(declare-fun |block_11_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (block_10_f_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (and (= expr_18_1 (> expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 0) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 v_6_1) true)))))) (and (not expr_18_1) (= error_1 1))) (block_11_function_f__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (block_11_function_f__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (summary_3_function_f__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (block_10_f_21_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (and (= error_1 error_0) (and (= expr_18_1 (> expr_16_0 expr_17_0)) (and (=> true true) (and (= expr_17_0 0) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (= expr_16_0 v_6_1) true))))))) true) (block_7_return_function_f__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (block_7_return_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) true) true) (summary_3_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1))))


(declare-fun |block_12_function_f__22_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Bool |state_type| Bool Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(block_12_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (block_12_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1 v_6_1) (and (summary_3_function_f__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 b_2_1 state_3 b_2_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 2562959041)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 152)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 195)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 166)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 193)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) true) (and true (= b_2_1 b_2_0))) true))))))) true) (summary_4_function_f__22_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_3 b_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (interface_0_C_23_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1) (= error_0 0))) (interface_0_C_23_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |contract_initializer_13_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(declare-fun |contract_initializer_entry_14_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) true) (contract_initializer_entry_14_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |contract_initializer_after_init_15_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (contract_initializer_entry_14_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_after_init_15_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (contract_initializer_after_init_15_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) true) (contract_initializer_13_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(declare-fun |implicit_constructor_entry_16_C_23_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) true) true) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_16_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (implicit_constructor_entry_16_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (contract_initializer_13_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true)) (> error_1 0)) (summary_constructor_2_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (implicit_constructor_entry_16_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) (and (= error_1 0) (and (contract_initializer_13_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2) true))) true) (summary_constructor_2_C_23_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (summary_constructor_2_C_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_23_0 this_0 abi_0 crypto_0 state_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> (and (and (interface_0_C_23_0 this_0 abi_0 crypto_0 state_0) true) (and (summary_4_function_f__22_23_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 b_2_0 state_1 b_2_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (abi_0 |abi_type|) (b_2_0 Bool) (b_2_1 Bool) (b_2_2 Bool) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_7_0 Int) (expr_9_0 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (v_6_0 Int) (v_6_1 Int) (v_6_2 Int))
(=> error_target_3_0 false)))
(check-sat)