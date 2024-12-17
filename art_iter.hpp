// Copyright 2019-2024 Laurynas Biveinis
#ifndef UNODB_DETAIL_ART_ITER_HPP
#define UNODB_DETAIL_ART_ITER_HPP

//
// ART Iterator Implementation
//

//
// FIXME This can not be written using a lambda due to the types
// incorporated at the top of art.cpp in the top-level namespace. We
// need to push those types down into an appropriate unodb specific
// namespace before they can be included more broadly.  Therefore, for
// the moment this file is empty, the iterator accepts a functor
// rather than a lambda, and the iterator code is in art.cpp.
//

namespace unodb {
}
#endif // UNODB_DETAIL_ART_ITER_HPP
