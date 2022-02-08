(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_18_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_18_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int))
(=> (= error_0 0) (nondet_interface_1_C_18_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_0 x_2_0))))


(declare-fun |summary_3_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |summary_4_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (nondet_interface_1_C_18_0 error_0 this_0 abi_0 crypto_0 state_0 x_2_0 state_1 x_2_1) true) (and (= error_0 0) (summary_4_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 x_2_1 b_4_0 state_2 x_2_2 b_4_1))) (nondet_interface_1_C_18_0 error_1 this_0 abi_0 crypto_0 state_0 x_2_0 state_2 x_2_2))))


(declare-fun |block_5_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_6_f_16_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_5_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_5_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= b_4_1 b_4_0))) true)) true) (block_6_f_16_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1))))


(declare-fun |block_7_return_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(declare-fun |block_8_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_6_f_16_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (and (=> true true) (and (= expr_11_0 2) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 1461501637330902918203684832716283019655932542975))) (and (= expr_10_0 x_2_1) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 340282366920938463463374607431768211455))) (and (= expr_7_0 b_4_1) (and (and (>= b_4_1 0) (<= b_4_1 340282366920938463463374607431768211455)) true)))))))) (and (or (< expr_11_0 0) (>= expr_11_0 20)) (= error_1 1))) (block_8_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_8_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (summary_3_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1))))


(declare-fun |block_9_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_6_f_16_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 255))) (and (= expr_13_1 expr_12_2) (and (=> true (and (>= expr_12_2 0) (<= expr_12_2 255))) (and (= expr_12_2 (ite (< expr_11_0 20) (bv2nat (bvlshr (bvshl (ite (>= expr_10_0 0) ((_ int2bv 160) expr_10_0) (bvneg ((_ int2bv 160) (- expr_10_0)))) (ite (>= (* expr_11_0 8) 0) ((_ int2bv 160) (* expr_11_0 8)) (bvneg ((_ int2bv 160) (- (* expr_11_0 8)))))) (ite (>= 152 0) ((_ int2bv 160) 152) (bvneg ((_ int2bv 160) (- 152)))))) expr_12_0)) (and (= error_1 error_0) (and (=> true true) (and (= expr_11_0 2) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 1461501637330902918203684832716283019655932542975))) (and (= expr_10_0 x_2_1) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 340282366920938463463374607431768211455))) (and (= expr_7_0 b_4_1) (and (and (>= b_4_1 0) (<= b_4_1 340282366920938463463374607431768211455)) true))))))))))))) (and (or (< expr_13_1 0) (>= expr_13_1 16)) (= error_2 2))) (block_9_function_f__17_18_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (block_9_function_f__17_18_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (summary_3_function_f__17_18_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_6_f_16_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (and (=> true (and (>= expr_14_2 0) (<= expr_14_2 255))) (and (= expr_14_2 (ite (< expr_13_1 16) (bv2nat (bvlshr (bvshl (ite (>= expr_7_0 0) ((_ int2bv 128) expr_7_0) (bvneg ((_ int2bv 128) (- expr_7_0)))) (ite (>= (* expr_13_1 8) 0) ((_ int2bv 128) (* expr_13_1 8)) (bvneg ((_ int2bv 128) (- (* expr_13_1 8)))))) (ite (>= 120 0) ((_ int2bv 128) 120) (bvneg ((_ int2bv 128) (- 120)))))) expr_14_0)) (and (= error_2 error_1) (and (=> true (and (>= expr_13_1 0) (<= expr_13_1 255))) (and (= expr_13_1 expr_12_2) (and (=> true (and (>= expr_12_2 0) (<= expr_12_2 255))) (and (= expr_12_2 (ite (< expr_11_0 20) (bv2nat (bvlshr (bvshl (ite (>= expr_10_0 0) ((_ int2bv 160) expr_10_0) (bvneg ((_ int2bv 160) (- expr_10_0)))) (ite (>= (* expr_11_0 8) 0) ((_ int2bv 160) (* expr_11_0 8)) (bvneg ((_ int2bv 160) (- (* expr_11_0 8)))))) (ite (>= 152 0) ((_ int2bv 160) 152) (bvneg ((_ int2bv 160) (- 152)))))) expr_12_0)) (and (= error_1 error_0) (and (=> true true) (and (= expr_11_0 2) (and (=> true (and (>= expr_10_0 0) (<= expr_10_0 1461501637330902918203684832716283019655932542975))) (and (= expr_10_0 x_2_1) (and (=> true (and (>= expr_7_0 0) (<= expr_7_0 340282366920938463463374607431768211455))) (and (= expr_7_0 b_4_1) (and (and (>= b_4_1 0) (<= b_4_1 340282366920938463463374607431768211455)) true)))))))))))))))) true) (block_7_return_function_f__17_18_0 error_2 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_7_return_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) true) true) (summary_3_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1))))


(declare-fun |block_10_function_f__17_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(block_10_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1)))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (block_10_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (and (summary_3_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 x_2_1 b_4_1 state_3 x_2_2 b_4_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_3_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_3_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_3_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_3_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 1205704916)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 71)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 221)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 152)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 212)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= b_4_1 b_4_0))) true))))))) true) (summary_4_function_f__17_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_3 x_2_2 b_4_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (interface_0_C_18_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (= error_0 0))) (interface_0_C_18_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |contract_initializer_11_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_12_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (contract_initializer_entry_12_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |contract_initializer_after_init_13_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_entry_12_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_after_init_13_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (contract_initializer_after_init_13_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) true) (contract_initializer_11_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(declare-fun |implicit_constructor_entry_14_C_18_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= x_2_1 x_2_0))) (and true (= x_2_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_14_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_14_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (contract_initializer_11_C_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true)) (> error_1 0)) (summary_constructor_2_C_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (implicit_constructor_entry_14_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) (and (= error_1 0) (and (contract_initializer_11_C_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 x_2_1 x_2_2) true))) true) (summary_constructor_2_C_18_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 x_2_0 x_2_2))))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (summary_constructor_2_C_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 x_2_0 x_2_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_18_0 this_0 abi_0 crypto_0 state_1 x_2_1))))


(declare-fun |error_target_4_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (interface_0_C_18_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (= error_0 1))) error_target_4_0)))


(declare-fun |error_target_5_0| () Bool)
(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> (and (and (interface_0_C_18_0 this_0 abi_0 crypto_0 state_0 x_2_0) true) (and (summary_4_function_f__17_18_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 x_2_0 b_4_0 state_1 x_2_1 b_4_1) (= error_0 2))) error_target_5_0)))


(assert
(forall ( (abi_0 |abi_type|) (b_4_0 Int) (b_4_1 Int) (b_4_2 Int) (crypto_0 |crypto_type|) (error_0 Int) (error_1 Int) (error_2 Int) (expr_10_0 Int) (expr_11_0 Int) (expr_12_0 Int) (expr_12_1 Int) (expr_12_2 Int) (expr_13_1 Int) (expr_14_0 Int) (expr_14_1 Int) (expr_14_2 Int) (expr_7_0 Int) (funds_3_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|) (x_2_0 Int) (x_2_1 Int) (x_2_2 Int))
(=> error_target_5_0 false)))
(check-sat)