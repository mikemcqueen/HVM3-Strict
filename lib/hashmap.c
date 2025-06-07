// hashmap.c - Implementation - Claude 4.0 generated
#include "hashmap.h"
#include <stdio.h>
#include <stdlib.h>

#define HASHMAP_INITIAL_SIZE 32768
#define HASHMAP_LOAD_FACTOR 0.75

// Internal structures - hidden from users
typedef struct {
    uint32_t key;
    void *value;
    bool occupied;
} hashmap_entry_t;

struct hashmap {
    hashmap_entry_t *entries;
    size_t size;
    size_t capacity;
};

// Hash function for 32-bit integers
static uint32_t hash_uint32(uint32_t key) {
  key ^= key >> 16;
  key *= 0x85ebca6b;
  key ^= key >> 13;
  key *= 0xc2b2ae35;
  key ^= key >> 16;
  return key;
}

// Find entry index for key (or where it should be inserted)
static size_t find_entry(hashmap_entry_t *entries, size_t capacity, uint32_t key) {
    uint32_t hash = hash_uint32(key);
    size_t index = hash % capacity;
    size_t start = index;
    
    do {
        if (!entries[index].occupied || entries[index].key == key) {
            return index;
        }
        index = (index + 1) % capacity;
    } while (index != start);
    
    // Should never reach here if load factor is maintained properly
    return index;
}

// Resize hash map when load factor is exceeded
static bool hashmap_resize(hashmap_t *map) {
    hashmap_entry_t *old_entries = map->entries;
    size_t old_capacity = map->capacity;
    
    map->capacity *= 2;
    map->entries = calloc(map->capacity, sizeof(hashmap_entry_t));
    if (!map->entries) {
        map->entries = old_entries;
        map->capacity = old_capacity;
        return false;
    }
    
    // Direct rehash without going through insert
    for (size_t i = 0; i < old_capacity; i++) {
        if (old_entries[i].occupied) {
            uint32_t hash = hash_uint32(old_entries[i].key);
            size_t index = hash % map->capacity;
            
            // Linear probe to find empty slot
            while (map->entries[index].occupied) {
                index = (index + 1) % map->capacity;
            }
            
            map->entries[index] = old_entries[i];
        }
    }
    
    free(old_entries);
    return true;
}

// Initialize hash map
hashmap_t* hashmap_create(void) {
    hashmap_t *map = malloc(sizeof(hashmap_t));
    if (!map) return NULL;
    
    map->entries = calloc(HASHMAP_INITIAL_SIZE, sizeof(hashmap_entry_t));
    if (!map->entries) {
        free(map);
        return NULL;
    }
    
    map->size = 0;
    map->capacity = HASHMAP_INITIAL_SIZE;
    return map;
}

// Insert key-value pair
bool hashmap_insert(hashmap_t *map, uint32_t key, void *value) {
    if (!map) return false;
    
    // Try to resize if load factor exceeded, but continue even if it fails
    if ((double)map->size / map->capacity >= HASHMAP_LOAD_FACTOR) {
        hashmap_resize(map); // Ignore return value
    }
    
    // Check if table is completely full
    if (map->size >= map->capacity) {
        return false; // Can't insert into full table
    }
    
    size_t index = find_entry(map->entries, map->capacity, key);
    
    // Update existing key
    if (map->entries[index].occupied) {
        map->entries[index].value = value;
        return true;
    }
    
    // Insert new key
    map->entries[index].key = key;
    map->entries[index].value = value;
    map->entries[index].occupied = true;
    
    map->size++;
    return true;
}

// Lookup value by key
void* hashmap_lookup(hashmap_t *map, uint32_t key) {
    if (!map) return NULL;
    
    size_t index = find_entry(map->entries, map->capacity, key);
    
    if (map->entries[index].occupied) {
        return map->entries[index].value;
    }
    
    return NULL;
}

// Clean up hash map
void hashmap_destroy(hashmap_t *map) {
    if (!map) return;
    
    free(map->entries);
    free(map);
}

#if 0
// Example usage
int main(void) {
    hashmap_t *map = hashmap_create();
    if (!map) {
        printf("Failed to create hash map\n");
        return 1;
    }
    
    // Insert some values
    uint32_t keys[] = {1001, 2002, 3003, 4004};
    char *values[] = {"Alice", "Bob", "Charlie", "Diana"};
    
    for (int i = 0; i < 4; i++) {
        if (!hashmap_insert(map, keys[i], values[i])) {
            printf("Failed to insert key %u\n", keys[i]);
        }
    }
    
    // Lookup values
    for (int i = 0; i < 4; i++) {
        char *name = (char*)hashmap_lookup(map, keys[i]);
        if (name) {
            printf("Key %u: %s\n", keys[i], name);
        } else {
            printf("Key %u: not found\n", keys[i]);
        }
    }
    
    // Test non-existent key
    char *result = (char*)hashmap_lookup(map, 9999);
    printf("Key 9999: %s\n", result ? result : "not found");
    
    hashmap_destroy(map);
    return 0;
}
#endif
