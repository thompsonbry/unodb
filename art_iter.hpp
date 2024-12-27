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

inline bool db::iterator::valid() const noexcept { return ! stack_.empty(); }

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

inline detail::node_ptr db::iterator::current_node() noexcept {
  return stack_.empty()
      ? detail::node_ptr(nullptr)
      : std::get<NP>( stack_.top() );
  ;
}

// inline db::iterator db::seek(const key search_key, bool& match, bool fwd) noexcept {
//   return end().seek( search_key, match, fwd);
// }

inline key db::visitor::get_key() noexcept {return it.get_key().value();}
inline value_view db::visitor::get_value() const noexcept {return it.get_val().value();}

template <typename FN>
inline void db::scan(FN fn, bool fwd) noexcept {
  if ( empty() ) return;
  if ( fwd ) {
    auto it { begin() };
    visitor v{ it };
    while ( it.valid() ) {
      if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
      it.next();
    }
  } else {
    auto it { last() };
    visitor v { it };
    while ( it.valid() ) {
      if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
      it.prior();
    }
  }
}

template <typename FN>
inline void db::scan(const key fromKey_, FN fn, bool fwd) noexcept {
  if ( empty() ) return;
  const detail::art_key fromKey{fromKey_};  // convert to internal key
  bool match {};
  if ( fwd ) {
    auto it { end().seek( fromKey, match, true/*fwd*/ ) };
    visitor v { it };
    while ( it.valid() ) {
      if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
      it.next();
    }
  } else {
    auto it { end().seek( fromKey, match, false/*fwd*/ ) };
    visitor v { it };
    while ( it.valid() ) {
      if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
      it.prior();
    }
  }
}

template <typename FN>
inline void db::scan(const key fromKey_, const key toKey_, FN fn) noexcept {
  if ( empty() ) return;
  const detail::art_key fromKey{fromKey_};  // convert to internal key
  const detail::art_key toKey{toKey_};      // convert to internal key
  const auto ret = fromKey.cmp( toKey );    // compare the internal keys.
  const bool fwd { ret < 0 };               // fromKey is less than toKey
  if ( ret == 0 ) return;                   // NOP if fromKey == toKey since toKey is exclusive upper bound.
  bool match {};
  if ( fwd ) {
    auto it1 { end().seek( fromKey, match, true/*fwd*/ ) }; // lower bound
    auto it2 { end().seek( toKey, match, false/*fwd*/ ) }; // upper bound
    std::cerr<<"scan:: fwd"<<std::endl;         // FIXME REMOVE DEBUG LINES.
    std::cerr<<"scan:: fromKey="<<fromKey_<<std::endl; it1.dump(std::cerr);
    std::cerr<<"scan:: toKey="<<fromKey_<<std::endl; it2.dump(std::cerr);
    visitor v { it1 };
    while ( it1.valid() ) {
      if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
      it1.next();
      if ( UNODB_DETAIL_UNLIKELY( it1.current_node() == it2.current_node() ) ) break;
    }
  } else {
    auto it1 { end().seek( fromKey, match, true/*fwd*/ ) }; // upper bound
    auto it2 { end().seek( toKey, match, false/*fwd*/ ) }; // upper bound
    std::cerr<<"scan:: rev"<<std::endl;         // FIXME REMOVE DEBUG LINES.
    std::cerr<<"scan:: fromKey="<<fromKey_<<std::endl; it1.dump(std::cerr);
    std::cerr<<"scan:: toKey="<<fromKey_<<std::endl; it2.dump(std::cerr);
    visitor v { it1 };
    while ( it1.valid() ) {
      if ( UNODB_DETAIL_UNLIKELY( fn( v ) ) ) break;
      it1.prior();
      if ( UNODB_DETAIL_UNLIKELY( it1.current_node() == it2.current_node() ) ) break;
    }
  }
}

} // namespace unodb

#endif // UNODB_DETAIL_ART_ITER_HPP
