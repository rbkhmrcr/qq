#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>

void generate_ristretto_random(uint8_t *buf, size_t len);

void generate_ristretto_range_proof(const uint64_t *vals,
                                    size_t vals_len,
                                    const uint8_t *blinding_factors,
                                    size_t blinding_factors_len,
                                    uint8_t *proof_buf,
                                    size_t proof_buf_len,
                                    uint8_t *commitments,
                                    size_t commitments_len);

bool verify_ristretto_range_proof(const uint8_t *proof_buf,
                                  size_t proof_buf_len,
                                  const uint8_t *commitments,
                                  size_t commitments_len);