// Copyright 2025 UnoDB contributors

// Example: CAS upsert operations — insert-or-resolve, update, and erase.
// Demonstrates the upsert API's three actions on an OLC concurrent ART.

#include "global.hpp"

#include <cstdint>
#include <iostream>
#include <string_view>
#include <tuple>

#include "art_common.hpp"
#include "olc_art.hpp"
#include "qsbr.hpp"

namespace {

using Db = unodb::olc_db<std::uint64_t, unodb::value_view>;

[[nodiscard, gnu::pure]] unodb::value_view from_sv(std::string_view sv) {
  return {reinterpret_cast<const std::byte*>(sv.data()), sv.length()};
}

}  // namespace

int main() {
  Db db;

  // --- Insert-or-resolve: key absent → inserts, returns true ---
  {
    unodb::quiescent_state_on_scope_exit qstate{};
    const bool inserted = db.upsert(1, from_sv("hello"), [](auto& /*v*/) {
      return unodb::upsert_action::keep;  // not called — key absent
    });
    std::cout << "upsert(1, \"hello\"): inserted=" << inserted << "\n";
  }

  // --- Keep: key present, lambda sees value, returns keep → no change ---
  {
    unodb::quiescent_state_on_scope_exit qstate{};
    const bool inserted = db.upsert(1, from_sv("world"), [](auto& /*v*/) {
      return unodb::upsert_action::keep;
    });
    std::cout << "upsert(1, keep): inserted=" << inserted << "\n";
    // Value is still "hello".
  }

  // --- Update: key present, lambda returns update → replace with proposed ---
  // For value_view: the proposed value (second arg) replaces the existing one.
  {
    unodb::quiescent_state_on_scope_exit qstate{};
    const bool inserted = db.upsert(1, from_sv("updated"), [](auto& /*v*/) {
      // Lambda observes existing value ("hello") and decides to update.
      // The proposed value "updated" is installed in the tree.
      return unodb::upsert_action::update;
    });
    std::cout << "upsert(1, \"updated\", update): inserted=" << inserted
              << "\n";
    // Value is now "updated".
  }

  // --- Update with typed value: lambda modifies the local copy ---
  // For typed values (e.g., uint64_t), the lambda can mutate the value.
  {
    unodb::olc_db<std::uint64_t, std::uint64_t> idb;
    {
      unodb::quiescent_state_on_scope_exit qstate{};
      std::ignore = idb.upsert(42, std::uint64_t{100}, [](auto& /*v*/) {
        return unodb::upsert_action::keep;  // inserts 100
      });
    }
    {
      unodb::quiescent_state_on_scope_exit qstate{};
      const bool inserted = idb.upsert(42, std::uint64_t{0}, [](auto& v) {
        // v is the existing value (100); modify it and return update
        // to write the new value back.
        v += 50;
        return unodb::upsert_action::update;
      });
      std::cout << "upsert(42, update v+=50): inserted=" << inserted << "\n";
    }
    {
      unodb::quiescent_state_on_scope_exit qstate{};
      const auto val = idb.get(42);
      std::cout << "  get(42) after update=" << (val ? *val : 0) << "\n";
    }
  }

  // --- Erase: key present, lambda returns erase → CAS remove ---
  {
    unodb::quiescent_state_on_scope_exit qstate{};
    const bool inserted = db.upsert(1, from_sv("unused"), [](auto& /*v*/) {
      return unodb::upsert_action::erase;
    });
    std::cout << "upsert(1, erase): inserted=" << inserted << "\n";
    // Key 1 is now removed from the tree.
  }

  // --- Verify key is gone ---
  {
    unodb::quiescent_state_on_scope_exit qstate{};
    const auto result = db.get(1);
    std::cout << "get(1) after erase: found=" << result.has_value() << "\n";
  }

  // --- Re-insert via upsert (key absent again) ---
  {
    unodb::quiescent_state_on_scope_exit qstate{};
    const bool inserted = db.upsert(1, from_sv("back"), [](auto& /*v*/) {
      return unodb::upsert_action::keep;
    });
    std::cout << "upsert(1, \"back\"): inserted=" << inserted << "\n";
  }
}
