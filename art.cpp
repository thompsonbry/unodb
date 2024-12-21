// Copyright 2019-2024 Laurynas Biveinis

#include "global.hpp"

#include "art.hpp"

#include <cstddef>
#include <iostream>
#include <optional>
#include <type_traits>
#include <utility>

#include "art_common.hpp"
#include "art_internal.hpp"
#include "art_internal_impl.hpp"
#include "assert.hpp"
#include "in_fake_critical_section.hpp"
#include "node_type.hpp"

namespace {

using leaf = unodb::detail::basic_leaf<unodb::detail::node_header>;

}  // namespace

namespace unodb::detail {

struct impl_helpers {
  // GCC 10 diagnoses parameters that are present only in uninstantiated if
  // constexpr branch, such as node_in_parent for inode_256.
  UNODB_DETAIL_DISABLE_GCC_10_WARNING("-Wunused-parameter")

  template <class INode>
  [[nodiscard]] static detail::node_ptr *add_or_choose_subtree(
      INode &inode, std::byte key_byte, art_key k, value_view v,
      db &db_instance, tree_depth depth, detail::node_ptr *node_in_parent);

  UNODB_DETAIL_RESTORE_GCC_10_WARNINGS()

  template <class INode>
  [[nodiscard]] static std::optional<detail::node_ptr *>
  remove_or_choose_subtree(INode &inode, std::byte key_byte, detail::art_key k,
                           db &db_instance, detail::node_ptr *node_in_parent);

  impl_helpers() = delete;
};

class [[nodiscard]] inode_4 final
    : public unodb::detail::basic_inode_4<unodb::detail::art_policy> {
 public:
  // NOLINTNEXTLINE(cppcoreguidelines-rvalue-reference-param-not-moved)
  using basic_inode_4::basic_inode_4;

  template <typename... Args>
  [[nodiscard]] auto add_or_choose_subtree(Args &&...args) {
    return unodb::detail::impl_helpers::add_or_choose_subtree(
        *this, std::forward<Args>(args)...);
  }

  template <typename... Args>
  [[nodiscard]] auto remove_or_choose_subtree(Args &&...args) {
    return unodb::detail::impl_helpers::remove_or_choose_subtree(
        *this, std::forward<Args>(args)...);
  }
};

#ifndef _MSC_VER
static_assert(sizeof(inode_4) == 48);
#else
// MSVC pads the first field to 8 byte boundary even though its natural
// alignment is 4 bytes, maybe due to parent class sizeof
static_assert(sizeof(inode_4) == 56);
#endif

class [[nodiscard]] inode_16 final
    : public unodb::detail::basic_inode_16<unodb::detail::art_policy> {
 public:
  // NOLINTNEXTLINE(cppcoreguidelines-rvalue-reference-param-not-moved)
  using basic_inode_16::basic_inode_16;

  template <typename... Args>
  [[nodiscard]] auto add_or_choose_subtree(Args &&...args) {
    return unodb::detail::impl_helpers::add_or_choose_subtree(
        *this, std::forward<Args>(args)...);
  }

  template <typename... Args>
  [[nodiscard]] auto remove_or_choose_subtree(Args &&...args) {
    return unodb::detail::impl_helpers::remove_or_choose_subtree(
        *this, std::forward<Args>(args)...);
  }
};

static_assert(sizeof(inode_16) == 160);

class [[nodiscard]] inode_48 final
    : public unodb::detail::basic_inode_48<unodb::detail::art_policy> {
 public:
  // NOLINTNEXTLINE(cppcoreguidelines-rvalue-reference-param-not-moved)
  using basic_inode_48::basic_inode_48;

  template <typename... Args>
  [[nodiscard]] auto add_or_choose_subtree(Args &&...args) {
    return unodb::detail::impl_helpers::add_or_choose_subtree(
        *this, std::forward<Args>(args)...);
  }

  template <typename... Args>
  [[nodiscard]] auto remove_or_choose_subtree(Args &&...args) {
    return unodb::detail::impl_helpers::remove_or_choose_subtree(
        *this, std::forward<Args>(args)...);
  }
};

#ifdef UNODB_DETAIL_AVX2
static_assert(sizeof(inode_48) == 672);
#else
static_assert(sizeof(inode_48) == 656);
#endif

class [[nodiscard]] inode_256 final
    : public unodb::detail::basic_inode_256<unodb::detail::art_policy> {
 public:
  // NOLINTNEXTLINE(cppcoreguidelines-rvalue-reference-param-not-moved)
  using basic_inode_256::basic_inode_256;

  template <typename... Args>
  [[nodiscard]] auto add_or_choose_subtree(Args &&...args) {
    return unodb::detail::impl_helpers::add_or_choose_subtree(
        *this, std::forward<Args>(args)...);
  }

  template <typename... Args>
  [[nodiscard]] auto remove_or_choose_subtree(Args &&...args) {
    return unodb::detail::impl_helpers::remove_or_choose_subtree(
        *this, std::forward<Args>(args)...);
  }
};

static_assert(sizeof(inode_256) == 2064);

}  // namespace unodb::detail

namespace {

// Because we cannot dereference, load(), & take address of - it is a temporary
// by then
UNODB_DETAIL_DISABLE_MSVC_WARNING(26490)
inline auto *unwrap_fake_critical_section(
    unodb::in_fake_critical_section<unodb::detail::node_ptr> *ptr) noexcept {
  return reinterpret_cast<unodb::detail::node_ptr *>(ptr);
}
UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

}  // namespace

namespace unodb::detail {

template <class INode>
detail::node_ptr *impl_helpers::add_or_choose_subtree(
    INode &inode, std::byte key_byte, art_key k, value_view v, db &db_instance,
    tree_depth depth, detail::node_ptr *node_in_parent) {
  auto *const child =
      unwrap_fake_critical_section(inode.find_child(key_byte).second);

  if (child != nullptr) return child;

  auto aleaf = art_policy::make_db_leaf_ptr(k, v, db_instance);
  const auto children_count = inode.get_children_count();

  if constexpr (!std::is_same_v<INode, inode_256>) {
    if (UNODB_DETAIL_UNLIKELY(children_count == INode::capacity)) {
      auto larger_node{INode::larger_derived_type::create(
          db_instance, inode, std::move(aleaf), depth)};
      *node_in_parent =
          node_ptr{larger_node.release(), INode::larger_derived_type::type};
#ifdef UNODB_DETAIL_WITH_STATS
      db_instance
          .template account_growing_inode<INode::larger_derived_type::type>();
#endif  // UNODB_DETAIL_WITH_STATS
      return child;
    }
  }
  inode.add_to_nonfull(std::move(aleaf), depth, children_count);
  return child;
}

template <class INode>
std::optional<detail::node_ptr *> impl_helpers::remove_or_choose_subtree(
    INode &inode, std::byte key_byte, detail::art_key k, db &db_instance,
    detail::node_ptr *node_in_parent) {
  const auto [child_i, child_ptr]{inode.find_child(key_byte)};

  if (child_ptr == nullptr) return {};

  const auto child_ptr_val{child_ptr->load()};
  if (child_ptr_val.type() != node_type::LEAF)
    return unwrap_fake_critical_section(child_ptr);

  const auto *const aleaf{child_ptr_val.template ptr<::leaf *>()};
  if (!aleaf->matches(k)) return {};

  if (UNODB_DETAIL_UNLIKELY(inode.is_min_size())) {
    if constexpr (std::is_same_v<INode, inode_4>) {
      auto current_node{
          art_policy::make_db_inode_unique_ptr(&inode, db_instance)};
      *node_in_parent = current_node->leave_last_child(child_i, db_instance);
    } else {
      auto new_node{
          INode::smaller_derived_type::create(db_instance, inode, child_i)};
      *node_in_parent =
          node_ptr{new_node.release(), INode::smaller_derived_type::type};
    }
#ifdef UNODB_DETAIL_WITH_STATS
    db_instance.template account_shrinking_inode<INode::type>();
#endif  // UNODB_DETAIL_WITH_STATS
    return nullptr;
  }

  inode.remove(child_i, db_instance);
  return nullptr;
}

}  // namespace unodb::detail

namespace unodb {

db::~db() noexcept { delete_root_subtree(); }

#ifdef UNODB_DETAIL_WITH_STATS

template <class INode>
constexpr void db::increment_inode_count() noexcept {
  static_assert(unodb::detail::inode_defs::is_inode<INode>());

  ++node_counts[as_i<INode::type>];
  increase_memory_use(sizeof(INode));
}

template <class INode>
constexpr void db::decrement_inode_count() noexcept {
  static_assert(unodb::detail::inode_defs::is_inode<INode>());
  UNODB_DETAIL_ASSERT(node_counts[as_i<INode::type>] > 0);

  --node_counts[as_i<INode::type>];
  decrease_memory_use(sizeof(INode));
}

template <node_type NodeType>
constexpr void db::account_growing_inode() noexcept {
  static_assert(NodeType != node_type::LEAF);

  // NOLINTNEXTLINE(google-readability-casting)
  ++growing_inode_counts[internal_as_i<NodeType>];
  UNODB_DETAIL_ASSERT(growing_inode_counts[internal_as_i<NodeType>] >=
                      node_counts[as_i<NodeType>]);
}

template <node_type NodeType>
constexpr void db::account_shrinking_inode() noexcept {
  static_assert(NodeType != node_type::LEAF);

  ++shrinking_inode_counts[internal_as_i<NodeType>];
  UNODB_DETAIL_ASSERT(shrinking_inode_counts[internal_as_i<NodeType>] <=
                      growing_inode_counts[internal_as_i<NodeType>]);
}

#endif  // UNODB_DETAIL_WITH_STATS

db::get_result db::get(key search_key) const noexcept {
  if (UNODB_DETAIL_UNLIKELY(root == nullptr)) return {};

  auto node{root};
  const detail::art_key k{search_key};
  auto remaining_key{k};

  while (true) {
    const auto node_type = node.type();
    if (node_type == node_type::LEAF) {
      const auto *const leaf{node.ptr<::leaf *>()};
      if (leaf->matches(k)) return leaf->get_value_view();
      return {};
    }

    UNODB_DETAIL_ASSERT(node_type != node_type::LEAF);

    auto *const inode{node.ptr<detail::inode *>()};
    const auto &key_prefix{inode->get_key_prefix()};
    const auto key_prefix_length{key_prefix.length()};
    if (key_prefix.get_shared_length(remaining_key) < key_prefix_length)
      return {};
    remaining_key.shift_right(key_prefix_length);
    const auto *const child{
        inode->find_child(node_type, remaining_key[0]).second};
    if (child == nullptr) return {};

    node = *child;
    remaining_key.shift_right(1);
  }
}

UNODB_DETAIL_DISABLE_MSVC_WARNING(26430)
bool db::insert(key insert_key, value_view v) {
  const auto k = detail::art_key{insert_key};

  if (UNODB_DETAIL_UNLIKELY(root == nullptr)) {
    auto leaf = unodb::detail::art_policy::make_db_leaf_ptr(k, v, *this);
    root = detail::node_ptr{leaf.release(), node_type::LEAF};
    return true;
  }

  auto *node = &root;
  detail::tree_depth depth{};
  auto remaining_key{k};

  while (true) {
    const auto node_type = node->type();
    if (node_type == node_type::LEAF) {
      auto *const leaf{node->ptr<::leaf *>()};
      const auto existing_key{leaf->get_key()};
      if (UNODB_DETAIL_UNLIKELY(k == existing_key)) return false;

      auto new_leaf = unodb::detail::art_policy::make_db_leaf_ptr(k, v, *this);
      auto new_node{detail::inode_4::create(*this, existing_key, remaining_key, depth,
                                            leaf, std::move(new_leaf))};
      *node = detail::node_ptr{new_node.release(), node_type::I4};
#ifdef UNODB_DETAIL_WITH_STATS
      account_growing_inode<node_type::I4>();
#endif  // UNODB_DETAIL_WITH_STATS
      return true;
    }

    UNODB_DETAIL_ASSERT(node_type != node_type::LEAF);
    UNODB_DETAIL_ASSERT(depth < detail::art_key::size);

    auto *const inode{node->ptr<detail::inode *>()};
    const auto &key_prefix{inode->get_key_prefix()};
    const auto key_prefix_length{key_prefix.length()};
    const auto shared_prefix_len{key_prefix.get_shared_length(remaining_key)};
    if (shared_prefix_len < key_prefix_length) {
      auto leaf = unodb::detail::art_policy::make_db_leaf_ptr(k, v, *this);
      auto new_node = detail::inode_4::create(*this, *node, shared_prefix_len, depth,
                                              std::move(leaf));
      *node = detail::node_ptr{new_node.release(), node_type::I4};
#ifdef UNODB_DETAIL_WITH_STATS
      account_growing_inode<node_type::I4>();
      ++key_prefix_splits;
      UNODB_DETAIL_ASSERT(growing_inode_counts[internal_as_i<node_type::I4>] >
                          key_prefix_splits);
#endif  // UNODB_DETAIL_WITH_STATS
      return true;
    }

    UNODB_DETAIL_ASSERT(shared_prefix_len == key_prefix_length);
    depth += key_prefix_length;
    remaining_key.shift_right(key_prefix_length);

    node = inode->add_or_choose_subtree<detail::node_ptr *>(
        node_type, remaining_key[0], k, v, *this, depth, node);

    if (node == nullptr) return true;

    ++depth;
    remaining_key.shift_right(1);
  }
}
UNODB_DETAIL_RESTORE_MSVC_WARNINGS()

bool db::remove(key remove_key) {
  const auto k = detail::art_key{remove_key};

  if (UNODB_DETAIL_UNLIKELY(root == nullptr)) return false;

  if (root.type() == node_type::LEAF) {
    auto *const root_leaf{root.ptr<leaf *>()};
    if (root_leaf->matches(k)) {
      const auto r{
        detail::art_policy::reclaim_leaf_on_scope_exit(root_leaf, *this)};
      root = nullptr;
      return true;
    }
    return false;
  }

  auto *node = &root;
  detail::tree_depth depth{};
  auto remaining_key{k};

  while (true) {
    const auto node_type = node->type();
    UNODB_DETAIL_ASSERT(node_type != node_type::LEAF);
    UNODB_DETAIL_ASSERT(depth < detail::art_key::size);

    auto *const inode{node->ptr<detail::inode *>()};
    const auto &key_prefix{inode->get_key_prefix()};
    const auto key_prefix_length{key_prefix.length()};
    const auto shared_prefix_len{key_prefix.get_shared_length(remaining_key)};
    if (shared_prefix_len < key_prefix_length) return false;

    UNODB_DETAIL_ASSERT(shared_prefix_len == key_prefix_length);
    depth += key_prefix_length;
    remaining_key.shift_right(key_prefix_length);

    const auto remove_result{
        inode->remove_or_choose_subtree<std::optional<detail::node_ptr *>>(
            node_type, remaining_key[0], k, *this, node)};
    if (UNODB_DETAIL_UNLIKELY(!remove_result)) return false;

    auto *const child_ptr{*remove_result};
    if (child_ptr == nullptr) return true;

    node = child_ptr;
    ++depth;
    remaining_key.shift_right(1);
  }
}

void db::delete_root_subtree() noexcept {
  if (root != nullptr) detail::art_policy::delete_subtree(root, *this);

#ifdef UNODB_DETAIL_WITH_STATS
  // It is possible to reset the counter to zero instead of decrementing it for
  // each leaf, but not sure the savings will be significant.
  UNODB_DETAIL_ASSERT(node_counts[as_i<node_type::LEAF>] == 0);
#endif  // UNODB_DETAIL_WITH_STATS
}

void db::clear() noexcept {
  delete_root_subtree();

  root = nullptr;
#ifdef UNODB_DETAIL_WITH_STATS
  current_memory_use = 0;
  node_counts[as_i<node_type::I4>] = 0;
  node_counts[as_i<node_type::I16>] = 0;
  node_counts[as_i<node_type::I48>] = 0;
  node_counts[as_i<node_type::I256>] = 0;
#endif  // UNODB_DETAIL_WITH_STATS
}

void db::dump(std::ostream &os) const {
#ifdef UNODB_DETAIL_WITH_STATS
  os << "db dump, current memory use = " << get_current_memory_use() << '\n';
#else
  os << "db dump\n";
#endif  // UNODB_DETAIL_WITH_STATS
  detail::art_policy::dump_node(os, root);
}

///
/// iterator
///

void db::iterator::dump(std::ostream &os) const {
  // Create a new stack and copy everything there.  Using the new
  // stack, print out the stack in top-bottom order.  This avoids
  // modifications to the existing stack for the iterator.
  std::stack<detail::inode_base::iter_result> tmp {};
  tmp = stack_;
  uint64_t level = tmp.size() - 1;
  while ( ! tmp.empty() ) {
    const auto& e = tmp.top();
    const auto np = std::get<NP>( e );
    const auto kb = std::get<KB>( e );
    const auto ci = std::get<CI>( e );
    std::string nt = "???";
    if(np.type()==node_type::LEAF) nt = "LEAF";
    if(np.type()==node_type::I4  ) nt = "I4  ";
    if(np.type()==node_type::I16 ) nt = "I16 ";
    if(np.type()==node_type::I48 ) nt = "I48 ";
    if(np.type()==node_type::I256) nt = "I256";
    os << "stack:: level = " << level;
    os << ", node at: " << np.template ptr<void *>()
       << ", tagged ptr = 0x" << std::hex << np.raw_val() << std::dec
       << ", type = " << nt
        ;
    if ( np.type() != node_type::LEAF ) {
      auto *const inode{ np.ptr<detail::inode *>() };
      os << ", key_byte = "<<static_cast<uint64_t>(kb)
         << ", child_index = "<<static_cast<uint64_t>(ci)
         << ", # children = "<<static_cast<std::uint64_t>(inode->get_children_count())
          ;
    }
    os << std::endl;
    tmp.pop();
    level--;
  }
}

// Traverse to the left-most leaf. The stack is cleared first and then
// re-populated as we step down along the path to the left-most leaf.
// If the tree is empty, then the result is the same as end().
db::iterator& db::iterator::first() noexcept {
  invalidate();  // clear the stack
  if (UNODB_DETAIL_UNLIKELY(db_.root == nullptr)) return *this;  // empty tree.
  auto node{ db_.root };
  while ( true ) {
    UNODB_DETAIL_ASSERT( node != nullptr );
    const auto node_type = node.type();
    if ( node_type == node_type::LEAF ) {
      // Mock up an iter_result for the leaf. The [key] and [child_index] are ignored for a leaf.
      stack_.push( { node, static_cast<std::byte>(0xFFU), static_cast<std::uint8_t>(0xFFU) } ); // push onto the stack.
      return *this; // done
    }
    // recursive descent.
    auto *const inode{ node.ptr<detail::inode *>() };
    auto e = inode->begin( node_type );  // first child of the current internal node.
    stack_.push( e );                    // push the entry on the stack.
    node = inode->get_child( node_type, std::get<CI>( e ) ); // get the child
  }
  UNODB_DETAIL_CANNOT_HAPPEN();
}

// Position the iterator on the next leaf in the index.
db::iterator& db::iterator::next() noexcept {
  if ( ! valid() ) return *this;  // the iterator is not positioned on anything.
  while ( ! stack_.empty() ) {
    auto e = stack_.top();
    auto node{ std::get<NP>( e ) };
    UNODB_DETAIL_ASSERT( node != nullptr );
    auto node_type = node.type();
    if ( node_type == node_type::LEAF ) {
      stack_.pop(); // pop off the leaf
      continue; // continue (if just a root leaf, we will fall through the loop since the stack will now be empty).
    }
    auto* inode{ node.ptr<detail::inode *>() };
    auto nxt = inode->next( node_type, std::get<CI>( e ) ); // next child of that parent.
    if ( ! nxt ) {
      stack_.pop();  // Nothing more for that inode.
      continue;      // We will look for the right sibling of the parent inode.
    }
    { // Recursive left descent.
      UNODB_DETAIL_ASSERT( nxt );  // value exists for std::optional.
      auto e2 = nxt.value();
      stack_.pop();
      stack_.push( e2 );
      node = inode->get_child( node_type, std::get<CI>( e2 ) );  // descend
      while ( true ) {
        UNODB_DETAIL_ASSERT( node != nullptr );
        node_type = node.type();
        if ( node_type == node_type::LEAF ) {
          // Mock up an iter_result for the leaf. The [key] and [child_index] are ignored for a leaf.
          stack_.push( { node, static_cast<std::byte>(0xFFU), static_cast<std::uint8_t>(0xFFU) } ); // push onto the stack.
          return *this;  // done
        }
        // recursive descent.
        inode = node.ptr<detail::inode *>();
        auto tmp = inode->begin( node_type );  // first child of the current internal node.
        stack_.push( tmp );                    // push the entry on the stack.
        node = inode->get_child( node_type, std::get<CI>( tmp ) ); // get the child
      }
    }
    UNODB_DETAIL_CANNOT_HAPPEN();
  }
  return *this; // stack is empty, so iterator == end().
}

#if 0

// Position the iterator on the prior leaf in the index.
db::iterator& db::iterator::prior() noexcept {
  UNODB_DETAIL_ASSERT( false );
  return *this;  // FIXME WRITE THE CODE.
}

// The find() logic is quite similar to ::get().  It is nearly the
// same code for the case where EQ semantics are used, but the
// iterator is positioned instead of returning the value for the key.
// The GTE and LTE cases would correspond to where get() is willing to
// return {} (leaf does not match, child pointer does not exist for
// key), but in this case the iterator is positioned before (LTE) or
// after (GTE) the missing key.
//
// FIXME REVIEW VERY CAREFULLY!
template <> bool it_t<db>::find(key search_key, find_enum dir) noexcept {
  
  if ( dir != find_enum::EQ ) return {}; // FIXME Support LTE, GTE

  invalidate();
  if (UNODB_DETAIL_UNLIKELY(db.root== nullptr)) return false;
  stack_entry cur { 0xFFU, 0xFFFFU, db.root }; // (key,child_index,root); key and child_index are ignore for the root.
  // auto node{ db_.root };
  // std::uint8_t child_index { 0 }; // child_index is ignored for the root node on the stack.
  const detail::art_key k{search_key};
  auto remaining_key{k};

  while (true) {
    stack_.push( cur );
    auto node = std::get<CP>( cur );
    const auto node_type = node.type();
    if (node_type == node_type::LEAF) {
      // Terminate on a leaf.
      const auto *const leaf{node.ptr<::leaf *>()};
      if (leaf->matches(k)) return true;  // This path handles EQ/LTE/GTE.
      // FIXME handle LT and GT here.
      return false;
    }
    UNODB_DETAIL_ASSERT(node_type != node_type::LEAF);
    // descent via an internal node.
    auto *const inode{node.ptr<::inode *>()};
    const auto &key_prefix{inode->get_key_prefix()};
    const auto key_prefix_length{key_prefix.length()};
    if (key_prefix.get_shared_length(remaining_key) < key_prefix_length) {
      return false; // FIXME Handle LTE here.
    }
    remaining_key.shift_right(key_prefix_length);
    auto res = inode->find_child(node_type, remaining_key[0]); 
    if (res.second == nullptr) return false;  // FIXME handle LT and GT here.
    stack_.push( { remaining_key[0], res.first, res.second } );
    // child_index = res.first;
    // node = *(res.second);
    remaining_key.shift_right(1);
  }
  UNODB_DETAIL_CANNOT_HAPPEN();
}

#ifdef RECURSIVE_SCAN
//
// FIXME This approach runs into problems when attempting to access
// the keys[] and children[] on the various internal node types.
// Those are all provide to the specific basic_inode_xxx class.  One
// way to handle this is to push down an abstraction for begin() and
// end() inode which delegates based on node type to its concrete
// implementations. If we do that, then it becomes easy to write
// first(), last(), and a for-each style loop over the children. The
// iterator could visit find_result (child_index, child_ptr).  But we
// also need to know the key for that child, so maybe a find_result3
// (key-byte, child_index, child_ptr). The problem with this approach
// is that it requires adding that iterator abstraction to each
// base_inode_xxx class to get started.
//
// FIXME Clarify current key vs recursive descent using the key.
// Basically, write the iterator to initially do a
// restart(internal_search_key), then scan.  Once we do OLC, it will
// restart(internal_current_key), then continue the scan.
//
// FIXME Must consume any prefix bytes in the leaf/node and the key
// byte along which we descend.
//
// FIXME This can be moved to art_internal_impl.hpp and realized there
// with a lambda.  That file is included by art.hpp.
//
// FIXME For OLC, must check version tag and restart when changed.
template <>
int it_t<db>::scan(detail::node_ptr node, uint32_t level, unodb::key& bkey, detail::art_key& ckey, detail::art_key rkey/*, it_functor fn*/) const noexcept {

  using inode4_type = typename inode_defs::n4;
  using inode16_type = typename inode_defs::n16;
  using inode48_type = typename inode_defs::n48;
  using inode256_type = typename inode_defs::n256;

  if ( node == nullptr ) return HALT;  // no tree.

  // Consider the current node.
  const auto node_type = node.type();

  if ( node_type == node_type::LEAF ) {
    // On a leaf.
    const auto *const leaf{node.ptr<::leaf *>()};
    bkey = leaf->get_key().decode(); // decode the key into the iterator's buffer.
    auto val = leaf->get_value_view();
    std::cerr<<"SCAN:: level="<<level<<", key="<<key_<<std::endl;
    // if ( ! fn( key_, val ) ) return HALT;  // invoke lamba, halting if it returns false.
    return CONTINUE; // pop the stack and continue the scan.
  }

  auto *const inode{node.ptr<::inode *>()};
#if 0
  const auto &key_prefix{inode->get_key_prefix()};
  const auto key_prefix_length{key_prefix.length()};
  if (key_prefix.get_shared_length(rkey) < key_prefix_length) {
    return false; // FIXME Handle LTE here.
  }
  rkey.shift_right(key_prefix_length);
  // FIXME How does descent to the current key followed by scan work?!?
  auto res = inode->find_child(node_type, remaining_key[0]);
#endif
  int res {HALT};  // result from recursive call (initially invalid).
  switch ( node_type ) {
    case node_type::I4: {
      const auto nchildren = inode->get_children_count();
      const inode4_type* i4 = reinterpret_cast<const inode4_type*>( inode );
      for (std::uint8_t i = 0; i < nchildren; i++ ) {
        unodb::detail::node_ptr child { &( i4->children[ i ] ) };
        res = scan( child, level+1, bkey, ckey, rkey/*, fn*/ );  // recursion
        if ( res != CONTINUE ) break;
      }
      break;
    }
    case node_type::I16: {
      const auto nchildren = inode->get_children_count();
      auto *const i16 = reinterpret_cast<inode16_type * const>( inode );
      for (std::uint8_t i = 0; i < nchildren; i++ ) {
        unodb::detail::node_ptr child { &( i16->children[ i ] ) };
        res = scan( child, level+1, bkey, ckey, rkey/*, fn*/ ); // recursion
        if ( res != CONTINUE ) break;
      }
      break;
    }
    case node_type::I48: {
      auto *const i48 = reinterpret_cast<inode48_type * const>( inode ); 
      for (std::uint16_t i = 0; i < 256; i++ ) {
        const auto child_i = i48->child_indexes[ static_cast<std::uint8_t>(i)].load();
        if ( child_i == inode48_type::empty_child ) continue;
        unodb::detail::node_ptr child { &( i48->children.pointer_array[ child_i ] ) };
        res = scan( child, level+1, bkey, ckey, rkey/*, fn*/ );  // recursion
        if ( res != CONTINUE ) break;
      }
      break;
    }
    case node_type::I256: {
      auto *const i256 = reinterpret_cast<inode256_type * const>( inode ); 
      for (std::uint16_t i = 0; i < 256; i++ ) {
        unodb::detail::node_ptr child { &( i256->children[ i ] ) };
        if ( child == nullptr ) continue;
        res = scan( child, level+1, bkey, ckey, rkey/*, fn*/ ); // recursion
        if ( res != CONTINUE ) break;
      }
      break;
    }
    default:
      UNODB_DETAIL_CANNOT_HAPPEN();
  }
  // If res == HALT, then we will pop all the way out and halt.
  // If res == RESTART, then we will pop all the way out and restart from the current key.
  // If res == CONTINUE, then we will pop out one level and see if there is more work to be done.
  return res;
}

template <>
void it_t<db>::scan(key search_key/*, it_functor fn*/) const noexcept {
  key bkey;                       // buffer for the materialized external key.
  detail::art_key ckey{search_key};  // convert to an internal key.
  auto rkey {ckey};
  int res = RESTART;
  while( res == RESTART ) {
    res = scan( db_.root, 0/*level*/, bkey, ckey, rkey/*, fn*/ ); // initiate forward scan from current key.
  }
  return; // TODO This assumes that CONTINUE is never returned by the scan() kernel.
}
#endif
#endif

}  // namespace unodb
