// Copyright 2019-2024 Laurynas Biveinis
#ifndef UNODB_DETAIL_ART_ITER_HPP
#define UNODB_DETAIL_ART_ITER_HPP

//
// ART Iterator Implementation
//

namespace unodb {

inline db::iterator& db::iterator::invalidate() noexcept {
  while ( ! stack_.empty() ) stack_.pop(); // clear the stack
  return *this;
}

inline std::optional<const key> db::iterator::get_key() noexcept {
  // FIXME Eventually this will need to use the stack to reconstruct
  // the key from the path from the root to this leaf.  Right now it
  // is relying on the fact that simple fixed width keys are stored
  // directly in the leaves.
  if ( ! valid() ) return {}; // not positioned on anything.
  const auto& e = stack_.top();
  const auto& node = std::get<NP>( e );
  UNODB_DETAIL_ASSERT( node.type() == node_type::LEAF ); // On a leaf.
  const auto *const leaf{ node.ptr<detail::leaf *>() }; // current leaf.
  key_ = leaf->get_key().decode(); // decode the key into the iterator's buffer.
  return key_; // return pointer to the internal key buffer.
}

inline std::optional<const value_view> db::iterator::get_val() const noexcept {
  if ( ! valid() ) return {}; // not positioned on anything.
  const auto& e = stack_.top();
  const auto& node = std::get<NP>( e );
  UNODB_DETAIL_ASSERT( node.type() == node_type::LEAF ); // On a leaf.
  const auto *const leaf{ node.ptr<detail::leaf *>() }; // current leaf.
  return leaf->get_value_view();
}

inline bool db::iterator::operator==(const iterator& other) const noexcept {
  if ( &db_ != &other.db_ ) return false;                     // different tree?
  if ( stack_.empty() != other.stack_.empty() ) return false; // one stack is empty and the other is not?
  if ( stack_.empty() ) return true;                          // both empty.
  // TODO Is this any different for OLC where there could be two
  // different tree structures and hence two iterators that point
  // at the same (key,val) in a leaf but there is a different
  // inode path?  In that case, this would say that the iterators
  // are not the same.  Which seems to be the correct answer. (The
  // main reason to compare iterators is to detect the end().)
  const auto& a = stack_.top();
  const auto& b = other.stack_.top();
  return a == b; // top of stack is same (inode, key, and child_index).
}

inline bool db::iterator::operator!=(const iterator& other) const noexcept { return !(*this == other); }

inline db::iterator db::seek(key search_key, bool& match, bool fwd) noexcept {
  return end().seek( search_key, match, fwd);
}

template <typename FN>
inline void db::scan(FN fn, bool fwd) noexcept {
  if ( fwd ) {
    auto it { begin() };
    while ( it.valid() && ! fn( it ) ) {
      it.next();
    }
  } else {
    auto it { last() };
    while ( it.valid() && ! fn( it ) ) {
      it.prior();
    }
  }
}

} // namespace unodb

#endif // UNODB_DETAIL_ART_ITER_HPP
