// hashmap.h - Public header - Claude 4.0 generated
#pragma once
#ifndef HASHMAP_H
#define HASHMAP_H

#include <stdint.h>
#include <stdbool.h>

// Opaque handle - users can't see the internals
typedef struct hashmap hashmap_t;

// Public API
hashmap_t* hashmap_create(void);
void hashmap_destroy(hashmap_t *map);
bool hashmap_insert(hashmap_t *map, uint32_t key, void *value);
void* hashmap_lookup(hashmap_t *map, uint32_t key);

#endif // HASHMAP_H

