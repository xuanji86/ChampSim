#include <algorithm>
#include <cassert>
#include <map>
#include <vector>
#include "skewed_prediction.h"
#include "cache.h"

class SamplingDeadBlockPredictor {
private:
    int kPredictorEntries = 4096;
    int kPredictorTables = 3;
    int kSamplerSets = 32;
    int kSamplerAssoc = 12;

    struct SamplerEntry {
        uint16_t partialTag : 15;
        uint16_t partialPC : 15;
        bool prediction : 1;
        bool valid : 1;
        uint8_t lru : 4;
    };

    struct PredictorEntry {
        uint8_t counter;
    };

    std::vector<SamplerEntry> sampler;
    std::vector<std::vector<PredictorEntry>> predictor;

    uint16_t signature(uint64_t pc) {
        return pc & 0x7FFF;
    }
    uint64_t hash(uint16_t sig, int table) {
        return (sig ^ (sig >> (table * 4))) % kPredictorEntries;
    }

public:
    SamplingDeadBlockPredictor(int numSets) : sampler(kSamplerSets * kSamplerAssoc),
                                               predictor(kPredictorTables, std::vector<PredictorEntry>(kPredictorEntries)) {
        assert(numSets % kSamplerSets == 0);
    }

    bool predict(uint64_t address, uint64_t pc) {
        uint32_t set = (address >> 6) % kSamplerSets;
        uint32_t tag = (address >> 12) & 0x7FFF;

        for (int i = 0; i < kSamplerAssoc; ++i) {
            SamplerEntry& entry = sampler[set * kSamplerAssoc + i];
            if (entry.valid && entry.partialTag == tag) {
                return entry.prediction;
            }
        }

        int confidence = 0;
        for (int i = 0; i < kPredictorTables; ++i) {
            uint16_t sig = signature(pc);
            uint64_t index = hash(sig, i);
            confidence += predictor[i][index].counter;
        }
        return confidence >= 8;
    }

    void update(uint64_t pc, uint64_t address, bool dead) {
        uint32_t partialPC = pc & 0x7FFF;
        uint32_t set = (address >> 6) % kSamplerSets;
        uint32_t tag = (address >> 12) & 0x7FFF;

        for (int i = 0; i < kSamplerAssoc; i++) {
            SamplerEntry& entry = sampler[set * kSamplerAssoc + i];
            if (entry.valid && entry.partialTag == tag) {
                entry.partialPC = partialPC;
                entry.prediction = dead;

                for (int j = 0; j < kSamplerAssoc; j++) {
                    if (sampler[set * kSamplerAssoc + j].lru < entry.lru) {
                        sampler[set * kSamplerAssoc + j].lru = std::min(sampler[set * kSamplerAssoc + j].lru + 1, 15);
                    }
                }
                entry.lru = 0;

                uint16_t sig = signature(pc);
                for (int k = 0; k < kPredictorTables; ++k) {
                    uint64_t index = hash(sig, k);
                    if (dead) {
                        predictor[k][index].counter = std::min(predictor[k][index].counter + 1, 3);
                    } else {
                        predictor[k][index].counter = std::max(predictor[k][index].counter - 1, 0);
                    }
                }
                return;
            }
        }

        int lru_index = 0;
        for (int i = 1; i < kSamplerAssoc; i++) {
            if (sampler[set * kSamplerAssoc + i].lru > sampler[set * kSamplerAssoc + lru_index].lru) {
                lru_index = i;
            }
        }

        SamplerEntry& entry = sampler[set * kSamplerAssoc + lru_index];
        entry.valid = true;
        entry.partialTag = tag;
        entry.partialPC = partialPC;
        entry.prediction = dead;
        for (int i = 0; i < kSamplerAssoc; i++) {
            if (sampler[set * kSamplerAssoc + i].lru < entry.lru) {
                sampler[set * kSamplerAssoc + i].lru = std::min(sampler[set * kSamplerAssoc + i].lru + 1, 15);
            }
        }
        entry.lru = 0;
    }
};

namespace {
    std::map<CACHE*, SamplingDeadBlockPredictor> predictors;
}

void CACHE::initialize_replacement() {
    predictors[this] = SamplingDeadBlockPredictor(NUM_SET);
}

uint32_t CACHE::find_victim(uint32_t triggering_cpu, uint64_t instr_id, uint32_t set, const BLOCK* current_set, uint64_t ip, uint64_t full_addr, uint32_t type) {
    auto& predictor = predictors[this];

    // Check if the current set is sampled
    bool is_sampled_set = (set % (NUM_SET / predictor.kSamplerSets)) == 0;

    if (is_sampled_set) {
        // If it is a sampled set, try to find a predicted dead block
        for (uint32_t way = 0; way < NUM_WAY; ++way) {
            if (predictor.predict(current_set[way].address, ip)) {
                return way;
            }
        }
    }

    // If no dead block is found or the set is not sampled, use LRU
    auto begin = std::next(std::begin(block), set * NUM_WAY);
    auto end = std::next(begin, NUM_WAY);
    auto victim = std::min_element(begin, end, [](const auto& a, const auto& b) { return a.lru < b.lru;});
    assert(begin <= victim && victim < end);
    return std::distance(begin, victim);
}

void CACHE::update_replacement_state(uint32_t triggering_cpu, uint32_t set, uint32_t way, uint64_t full_addr, uint64_t ip, uint64_t victim_addr, uint32_t type, uint8_t hit) {
    auto& predictor = predictors[this];

    block[set * NUM_WAY + way].lru = current_cycle;

    // Check if the current set is sampled
    bool is_sampled_set = (set % (NUM_SET / predictor.kSamplerSets)) == 0;

    if (is_sampled_set) {
        if (!hit || access_type{type} != access_type::WRITE) {
            predictor.update(ip, full_addr, false);
        } else {
            predictor.update(ip, victim_addr, true);
        }
    }
}

bool CACHE::should_bypass(uint64_t addr, uint64_t ip) {
    auto& predictor = predictors[this];
    return predictor.predict(addr, ip);
}

void CACHE::replacement_final_stats() {}


bool CACHE::handle_fill(const mshr_type& fill_mshr)
{
    cpu = fill_mshr.cpu;

    // Check if the block should be bypassed
    if (should_bypass(fill_mshr.address, fill_mshr.ip)) {
        // If predicted dead, perform bypassing
        // Do not insert the block into the cache, directly send the response
        auto metadata_thru = fill_mshr.pf_metadata;
        response_type response{fill_mshr.address, fill_mshr.v_address, fill_mshr.data, metadata_thru, fill_mshr.instr_depend_on_me};
        for (auto ret : fill_mshr.to_return)
            ret->push_back(response);

        // Update stats
        sim_stats.total_miss_latency += current_cycle - (fill_mshr.cycle_enqueued + 1);

        return true;
    }

    // Find victim
    auto [set_begin, set_end] = get_set_span(fill_mshr.address);
    auto way = std::find_if_not(set_begin, set_end, [](auto x) { return x.valid; });
    if (way == set_end)
        way = std::next(set_begin, impl_find_victim(fill_mshr.cpu, fill_mshr.instr_id, get_set_index(fill_mshr.address), &*set_begin, fill_mshr.ip,
                                                    fill_mshr.address, champsim::to_underlying(fill_mshr.type)));
    assert(set_begin <= way);
    assert(way <= set_end);
    const auto way_idx = static_cast<std::size_t>(std::distance(set_begin, way)); // cast protected by earlier assertion

    if constexpr (champsim::debug_print) {
        fmt::print(
            "[{}] {} instr_id: {} address: {:#x} v_address: {:#x} set: {} way: {} type: {} prefetch_metadata: {} cycle_enqueued: {} cycle: {}\n",
            NAME, __func__, fill_mshr.instr_id, fill_mshr.address, fill_mshr.v_address, get_set_index(fill_mshr.address), way_idx,
            access_type_names.at(champsim::to_underlying(fill_mshr.type)), fill_mshr.pf_metadata, fill_mshr.cycle_enqueued, current_cycle);
    }

    bool success = true;
    auto metadata_thru = fill_mshr.pf_metadata;
    auto pkt_address = (virtual_prefetch ? fill_mshr.v_address : fill_mshr.address) & ~champsim::bitmask(match_offset_bits ? 0 : OFFSET_BITS);
    if (way != set_end) {
        if (way->valid && way->dirty) {
            request_type writeback_packet;

            writeback_packet.cpu = fill_mshr.cpu;
            writeback_packet.address = way->address;
            writeback_packet.data = way->data;
            writeback_packet.instr_id = fill_mshr.instr_id;
            writeback_packet.ip = 0;
            writeback_packet.type = access_type::WRITE;
            writeback_packet.pf_metadata = way->pf_metadata;
            writeback_packet.response_requested = false;

            if constexpr (champsim::debug_print) {
                fmt::print("[{}] {} evict address: {:#x} v_address: {:#x} prefetch_metadata: {}\n", NAME,
                    __func__, writeback_packet.address, writeback_packet.v_address, fill_mshr.pf_metadata);
            }

            success = lower_level->add_wq(writeback_packet);
        }

        if (success) {
            auto evicting_address = (ever_seen_data ? way->address : way->v_address) & ~champsim::bitmask(match_offset_bits ? 0 : OFFSET_BITS);

            if (way->prefetch)
                ++sim_stats.pf_useless;

            if (fill_mshr.type == access_type::PREFETCH)
                ++sim_stats.pf_fill;

            *way = BLOCK{fill_mshr};

            metadata_thru = impl_prefetcher_cache_fill(pkt_address, get_set_index(fill_mshr.address), way_idx, fill_mshr.type == access_type::PREFETCH,
                                                       evicting_address, metadata_thru);
            impl_update_replacement_state(fill_mshr.cpu, get_set_index(fill_mshr.address), way_idx, fill_mshr.address, fill_mshr.ip, evicting_address,
                                          champsim::to_underlying(fill_mshr.type), false);

            way->pf_metadata = metadata_thru;
        }
    } else {
        // Bypass
        assert(fill_mshr.type != access_type::WRITE);

        metadata_thru =
            impl_prefetcher_cache_fill(pkt_address, get_set_index(fill_mshr.address), way_idx, fill_mshr.type == access_type::PREFETCH, 0, metadata_thru);
        impl_update_replacement_state(fill_mshr.cpu, get_set_index(fill_mshr.address), way_idx, fill_mshr.address, fill_mshr.ip, 0,
                                      champsim::to_underlying(fill_mshr.type), false);
    }

    if (success) {
        // COLLECT STATS
        sim_stats.total_miss_latency += current_cycle - (fill_mshr.cycle_enqueued + 1);

        response_type response{fill_mshr.address, fill_mshr.v_address, fill_mshr.data, metadata_thru, fill_mshr.instr_depend_on_me};
        for (auto ret : fill_mshr.to_return)
            ret->push_back(response);
    }

    return success;
}

bool CACHE::handle_miss(const tag_lookup_type& handle_pkt)
{
    if constexpr (champsim::debug_print) {
        fmt::print("[{}] {} instr_id: {} address: {:#x} v_address: {:#x} type: {} local_prefetch: {} cycle: {}\n", NAME, __func__,
                   handle_pkt.instr_id, handle_pkt.address, handle_pkt.v_address,
                   access_type_names.at(champsim::to_underlying(handle_pkt.type)), handle_pkt.prefetch_from_this, current_cycle);
    }

    mshr_type to_allocate{handle_pkt, current_cycle};

    cpu = handle_pkt.cpu;

    // Check mshr
    auto mshr_entry = std::find_if(std::begin(MSHR), std::end(MSHR), [match = handle_pkt.address >> OFFSET_BITS, shamt = OFFSET_BITS](const auto& entry) {
        return (entry.address >> shamt) == match;
    });
    bool mshr_full = (MSHR.size() == MSHR_SIZE);

    if (mshr_entry != MSHR.end()) // Miss already inflight
    {
        if (mshr_entry->type == access_type::PREFETCH && handle_pkt.type != access_type::PREFETCH) {
            // Mark the prefetch as useful
            if (mshr_entry->prefetch_from_this)
                ++sim_stats.pf_useful;
        }

        *mshr_entry = mshr_type::merge(*mshr_entry, to_allocate);
    } else {
        if (mshr_full) { // Not enough MSHR resources
            if constexpr (champsim::debug_print) {
                fmt::print("[{}] {} MSHR full\n", NAME, __func__);
            }

            // Check if the block should be bypassed
            if (should_bypass(handle_pkt.address, handle_pkt.ip)) {
                // If predicted dead and MSHR is full, perform bypassing
                // Do not send the request to the lower level cache, directly return
                return true;
            }

            return false;
        }

        request_type fwd_pkt;

        fwd_pkt.asid[0] = handle_pkt.asid[0];
        fwd_pkt.asid[1] = handle_pkt.asid[1];
        fwd_pkt.type = (handle_pkt.type == access_type::WRITE) ? access_type::RFO : handle_pkt.type;
        fwd_pkt.pf_metadata = handle_pkt.pf_metadata;
        fwd_pkt.cpu = handle_pkt.cpu;

        fwd_pkt.address = handle_pkt.address;
        fwd_pkt.v_address = handle_pkt.v_address;
        fwd_pkt.data = handle_pkt.data;
        fwd_pkt.instr_id = handle_pkt.instr_id;
        fwd_pkt.ip = handle_pkt.ip;

        fwd_pkt.instr_depend_on_me = handle_pkt.instr_depend_on_me;
        fwd_pkt.response_requested = (!handle_pkt.prefetch_from_this || !handle_pkt.skip_fill);

        bool success;
        if (prefetch_as_load || handle_pkt.type != access_type::PREFETCH)
            success = lower_level->add_rq(fwd_pkt);
        else
            success = lower_level->add_pq(fwd_pkt);

        if (!success) {
            if constexpr (champsim::debug_print) {
                fmt::print("[{}] {} could not send to lower\n", NAME, __func__);
            }

            return false;
        }

        // Allocate an MSHR
        if (fwd_pkt.response_requested) {
            MSHR.push_back(to_allocate);
            MSHR.back().pf_metadata = fwd_pkt.pf_metadata;
        }
    }

    ++sim_stats.misses[champsim::to_underlying(handle_pkt.type)][handle_pkt.cpu];

    return true;
}