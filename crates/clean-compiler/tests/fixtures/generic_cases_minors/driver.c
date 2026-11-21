/* Copyright 2026 Andrew Yates
 * SPDX-License-Identifier: Apache-2.0 */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    uint64_t input = strtoull(argv[1], NULL, 10);
    clean_obj* results[] = {
        l_runLeft(clean_nat_of_u64(input)),
        l_runRight(clean_nat_of_u64(input)),
        l_runPair(clean_nat_of_u64(input)),
        l_runFunctionLeft(clean_nat_of_u64(input)),
        l_runFunctionRight(clean_nat_of_u64(input)),
        l_runLambdaLong(clean_nat_of_u64(input)),
        l_runNone(clean_nat_of_u64(input))
    };
    for (size_t i = 0; i < sizeof(results) / sizeof(results[0]); i++) {
        unsigned __int128 value = clean_nat_to_u128(results[i]);
        if (value > UINT64_MAX) return 3;
        printf("%llu\n", (unsigned long long)value);
        clean_dec(results[i]);
    }
    return 0;
}
