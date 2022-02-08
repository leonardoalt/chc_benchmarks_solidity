(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
(declare-fun |interface_0_C_35_0| (Int |abi_type| |crypto_type| |state_type| Int ) Bool)
(declare-fun |nondet_interface_1_C_35_0| (Int Int |abi_type| |crypto_type| |state_type| Int |state_type| Int ) Bool)
(declare-fun |summary_constructor_2_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (error_0 Int) (state_0 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (= error_0 0) (nondet_interface_1_C_35_0 error_0 this_0 abi_0 crypto_0 state_0 d_6_0 state_0 d_6_0))))


(declare-fun |summary_3_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |summary_4_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_b_12_0 Int) (_b_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (nondet_interface_1_C_35_0 error_0 this_0 abi_0 crypto_0 state_0 d_6_0 state_1 d_6_1) true) (and (= error_0 0) (summary_4_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 d_6_1 _a_9_0 _b_12_0 state_2 d_6_2 _a_9_1 _b_12_1))) (nondet_interface_1_C_35_0 error_1 this_0 abi_0 crypto_0 state_0 d_6_0 state_2 d_6_2))))


(declare-fun |block_5_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_6_f_33_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_b_12_0 Int) (_b_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_5_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1)))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_b_12_0 Int) (_b_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_5_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= d_6_1 d_6_0))) (and (and true (= _a_9_1 _a_9_0)) (= _b_12_1 _b_12_0))) true)) true) (block_6_f_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1))))


(declare-fun |block_7_return_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(declare-fun |block_8_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_b_12_0 Int) (_b_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1) (and (= expr_30_1 (= expr_28_0 expr_29_0)) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 1))) (and (= expr_29_0 _b_12_1) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 1))) (and (= expr_28_0 d_6_1) (and (=> true expr_24_1) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 1))) (and (= expr_23_0 d_6_1) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 1))) (and (= expr_22_0 _a_9_1) (and (=> true expr_18_1) (and (= expr_18_1 (= expr_16_0 expr_17_0)) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 1))) (and (= expr_17_0 _b_12_1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 1))) (and (= expr_16_0 _a_9_1) (and (and (>= _b_12_1 0) (<= _b_12_1 1)) (and (and (>= _a_9_1 0) (<= _a_9_1 1)) true)))))))))))))))))))) (and (not expr_30_1) (= error_1 1))) (block_8_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1))))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_b_12_0 Int) (_b_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (block_8_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1) (summary_3_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1))))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_b_12_0 Int) (_b_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_6_f_33_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1) (and (= error_1 error_0) (and (= expr_30_1 (= expr_28_0 expr_29_0)) (and (=> true (and (>= expr_29_0 0) (<= expr_29_0 1))) (and (= expr_29_0 _b_12_1) (and (=> true (and (>= expr_28_0 0) (<= expr_28_0 1))) (and (= expr_28_0 d_6_1) (and (=> true expr_24_1) (and (= expr_24_1 (= expr_22_0 expr_23_0)) (and (=> true (and (>= expr_23_0 0) (<= expr_23_0 1))) (and (= expr_23_0 d_6_1) (and (=> true (and (>= expr_22_0 0) (<= expr_22_0 1))) (and (= expr_22_0 _a_9_1) (and (=> true expr_18_1) (and (= expr_18_1 (= expr_16_0 expr_17_0)) (and (=> true (and (>= expr_17_0 0) (<= expr_17_0 1))) (and (= expr_17_0 _b_12_1) (and (=> true (and (>= expr_16_0 0) (<= expr_16_0 1))) (and (= expr_16_0 _a_9_1) (and (and (>= _b_12_1 0) (<= _b_12_1 1)) (and (and (>= _a_9_1 0) (<= _a_9_1 1)) true))))))))))))))))))))) true) (block_7_return_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1))))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_b_12_0 Int) (_b_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_7_return_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1) true) true) (summary_3_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1))))


(declare-fun |block_9_function_f__34_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| Int Int Int |state_type| Int Int Int ) Bool)
(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_b_12_0 Int) (_b_12_1 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(block_9_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1)))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (block_9_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1) (and (summary_3_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_2 d_6_1 _a_9_1 _b_12_1 state_3 d_6_2 _a_9_2 _b_12_2) (and (= state_2 (|state_type| (store (|balances| state_1) this_0 (+ (select (|balances| state_1) this_0) funds_2_0)))) (and (and (>= (+ (select (|balances| state_1) this_0) funds_2_0) 0) (<= (+ (select (|balances| state_1) this_0) funds_2_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= funds_2_0 (|msg.value| tx_0)) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (and (and (and (and (and (= (|msg.value| tx_0) 0) (= (|msg.sig| tx_0) 514261825)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 0) 30)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 1) 167)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 2) 3)) (= (select (|bytes_tuple_accessor_array| (|msg.data| tx_0)) 3) 65)) (>= (|bytes_tuple_accessor_length| (|msg.data| tx_0)) 4))) (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= d_6_1 d_6_0))) (and (and true (= _a_9_1 _a_9_0)) (= _b_12_1 _b_12_0))) true))))))) true) (summary_4_function_f__34_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_3 d_6_2 _a_9_2 _b_12_2))))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_35_0 this_0 abi_0 crypto_0 state_0 d_6_0) true) (and (summary_4_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1) (= error_0 0))) (interface_0_C_35_0 this_0 abi_0 crypto_0 state_1 d_6_1))))


(declare-fun |contract_initializer_10_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(declare-fun |contract_initializer_entry_11_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (= state_1 state_0) (= error_0 0)) (and true (= d_6_1 d_6_0))) (contract_initializer_entry_11_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1))))


(declare-fun |contract_initializer_after_init_12_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_entry_11_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1) true) true) (contract_initializer_after_init_12_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1))))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (contract_initializer_after_init_12_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1) true) true) (contract_initializer_10_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1))))


(declare-fun |implicit_constructor_entry_13_C_35_0| (Int Int |abi_type| |crypto_type| |tx_type| |state_type| |state_type| Int Int ) Bool)
(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (and (and (= state_1 state_0) (= error_0 0)) (and true (= d_6_1 d_6_0))) (and true (= d_6_1 0))) (>= (select (|balances| state_1) this_0) (|msg.value| tx_0))) (implicit_constructor_entry_13_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1))))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_13_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1) (and (contract_initializer_10_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 d_6_1 d_6_2) true)) (> error_1 0)) (summary_constructor_2_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 d_6_0 d_6_2))))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (implicit_constructor_entry_13_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1) (and (= error_1 0) (and (contract_initializer_10_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_1 state_2 d_6_1 d_6_2) true))) true) (summary_constructor_2_C_35_0 error_1 this_0 abi_0 crypto_0 tx_0 state_0 state_2 d_6_0 d_6_2))))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (summary_constructor_2_C_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 state_1 d_6_0 d_6_1) true) (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (|block.basefee| tx_0) 0) (<= (|block.basefee| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935)) (and (>= (|block.chainid| tx_0) 0) (<= (|block.chainid| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.coinbase| tx_0) 0) (<= (|block.coinbase| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|block.difficulty| tx_0) 0) (<= (|block.difficulty| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.gaslimit| tx_0) 0) (<= (|block.gaslimit| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.number| tx_0) 0) (<= (|block.number| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|block.timestamp| tx_0) 0) (<= (|block.timestamp| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|msg.sender| tx_0) 0) (<= (|msg.sender| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|msg.value| tx_0) 0) (<= (|msg.value| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (and (>= (|tx.origin| tx_0) 0) (<= (|tx.origin| tx_0) 1461501637330902918203684832716283019655932542975))) (and (>= (|tx.gasprice| tx_0) 0) (<= (|tx.gasprice| tx_0) 115792089237316195423570985008687907853269984665640564039457584007913129639935))) (= (|msg.value| tx_0) 0)) (= error_0 0))) (interface_0_C_35_0 this_0 abi_0 crypto_0 state_1 d_6_1))))


(declare-fun |error_target_3_0| () Bool)
(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> (and (and (interface_0_C_35_0 this_0 abi_0 crypto_0 state_0 d_6_0) true) (and (summary_4_function_f__34_35_0 error_0 this_0 abi_0 crypto_0 tx_0 state_0 d_6_0 _a_9_0 _b_12_0 state_1 d_6_1 _a_9_1 _b_12_1) (= error_0 1))) error_target_3_0)))


(assert
(forall ( (_a_9_0 Int) (_a_9_1 Int) (_a_9_2 Int) (_b_12_0 Int) (_b_12_1 Int) (_b_12_2 Int) (abi_0 |abi_type|) (crypto_0 |crypto_type|) (d_6_0 Int) (d_6_1 Int) (d_6_2 Int) (error_0 Int) (error_1 Int) (expr_16_0 Int) (expr_17_0 Int) (expr_18_1 Bool) (expr_22_0 Int) (expr_23_0 Int) (expr_24_1 Bool) (expr_28_0 Int) (expr_29_0 Int) (expr_30_1 Bool) (funds_2_0 Int) (state_0 |state_type|) (state_1 |state_type|) (state_2 |state_type|) (state_3 |state_type|) (this_0 Int) (tx_0 |tx_type|))
(=> error_target_3_0 false)))
(check-sat)