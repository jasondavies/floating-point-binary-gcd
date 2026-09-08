#ifndef PARSE_DECIMAL_H
#define PARSE_DECIMAL_H

#include <stddef.h>
#include <stdint.h>

/* Decimal digits only: reject signs, whitespace, trailing text, and overflow. */
static inline int parse_decimal_u64(const char *text, uint64_t maximum, uint64_t *out) {
    uint64_t value = 0;
    if (text == NULL || *text == '\0') {
        return 0;
    }
    for (; *text != '\0'; ++text) {
        if (*text < '0' || *text > '9') {
            return 0;
        }
        unsigned digit = (unsigned)(*text - '0');
        if (digit > maximum || value > (maximum - digit) / 10) {
            return 0;
        }
        value = value * 10 + digit;
    }
    *out = value;
    return 1;
}

#endif
