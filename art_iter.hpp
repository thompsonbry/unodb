// Copyright 2019-2024 Laurynas Biveinis
#ifndef UNODB_DETAIL_ART_ITER_HPP
#define UNODB_DETAIL_ART_ITER_HPP
//
// ART Iterator Implementation
//
namespace unodb {

template <typename Db>
bool it_t<Db>::valid() const noexcept {
  // Note: A valid iterator must have a path to a leaf.
  return !stack_.empty() && ( stack_.top().second.type() == node_type::LEAF );
}


template <typename FN>
template <typename Db>
void it_t<Db> scan(key search_key, FN fn) const noexcept {
}

}
#endif // UNODB_DETAIL_ART_ITER_HPP
