extern crate proc_macro;
#[macro_use]
extern crate syn;
#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use syn::DeriveInput;

#[proc_macro_derive(PtrEq)]
pub fn derive_ptr_eq(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let (impl_gn, ty_gn, where_cl) = input.generics.split_for_impl();

    let expanded = quote! {
        unsafe impl #impl_gn PtrEq for #name #ty_gn #where_cl {}

        // &T

        impl #impl_gn ::core::hash::Hash for &#name #ty_gn #where_cl {
            fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
                ((*self) as *const (#name #ty_gn)).hash(state)
            }
        }

        // &mut T

        impl #impl_gn ::core::hash::Hash for &mut #name #ty_gn #where_cl {
            fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
                ((*self) as *const (#name #ty_gn)).hash(state)
            }
        }

        // &T and &T

        impl #impl_gn ::core::cmp::PartialEq<&#name #ty_gn> for &#name #ty_gn #where_cl {
            #[inline]
            fn eq(&self, other: &&#name #ty_gn) -> bool {
                ::core::ptr::eq(*self, *other)
            }
        }

        impl #impl_gn ::core::cmp::Eq for &#name #ty_gn #where_cl {}

        impl #impl_gn ::core::cmp::PartialOrd<&#name #ty_gn> for &#name #ty_gn #where_cl {
            #[inline]
            fn partial_cmp(&self, other: &&#name #ty_gn) -> ::core::option::Option<::core::cmp::Ordering> {
                ((*self) as *const (#name #ty_gn)).partial_cmp(&((*other) as *const (#name #ty_gn)))
            }
        }

        impl #impl_gn ::core::cmp::Ord for &#name #ty_gn #where_cl {
            #[inline]
            fn cmp(&self, other: &Self) -> ::core::cmp::Ordering {
                ((*self) as *const (#name #ty_gn)).cmp(&((*other) as *const (#name #ty_gn)))
            }
        }

        // &mut T and &mut T

        impl #impl_gn ::core::cmp::PartialEq<&mut #name #ty_gn> for &mut #name #ty_gn #where_cl {
            #[inline]
            fn eq(&self, other: &&mut #name #ty_gn) -> bool {
                ::core::ptr::eq(*self, *other)
            }
        }

        impl #impl_gn ::core::cmp::Eq for &mut #name #ty_gn #where_cl {}

        impl #impl_gn ::core::cmp::PartialOrd<&mut #name #ty_gn> for &mut #name #ty_gn #where_cl {
            #[inline]
            fn partial_cmp(&self, other: &&mut #name #ty_gn) -> ::core::option::Option<::core::cmp::Ordering> {
                ((*self) as *const (#name #ty_gn)).partial_cmp(&((*other) as *const (#name #ty_gn)))
            }
        }

        impl #impl_gn ::core::cmp::Ord for &mut #name #ty_gn #where_cl {
            #[inline]
            fn cmp(&self, other: &Self) -> ::core::cmp::Ordering {
                ((*self) as *const (#name #ty_gn)).cmp(&((*other) as *const (#name #ty_gn)))
            }
        }

        // &T and &mut T

        impl #impl_gn ::core::cmp::PartialEq<&mut #name #ty_gn> for &#name #ty_gn #where_cl {
            #[inline]
            fn eq(&self, other: &&mut #name #ty_gn) -> bool {
                ::core::ptr::eq(*self, *other)
            }
        }

        impl #impl_gn ::core::cmp::PartialOrd<&mut #name #ty_gn> for &#name #ty_gn #where_cl {
            #[inline]
            fn partial_cmp(&self, other: &&mut #name #ty_gn) -> ::core::option::Option<::core::cmp::Ordering> {
                ((*self) as *const (#name #ty_gn)).partial_cmp(&((*other) as *const (#name #ty_gn)))
            }
        }

        // &mut T and &T

        impl #impl_gn ::core::cmp::PartialEq<&#name #ty_gn> for &mut #name #ty_gn #where_cl {
            #[inline]
            fn eq(&self, other: &&#name #ty_gn) -> bool {
                ::core::ptr::eq(*self, *other)
            }
        }

        impl #impl_gn ::core::cmp::PartialOrd<&#name #ty_gn> for &mut #name #ty_gn #where_cl {
            #[inline]
            fn partial_cmp(&self, other: &&#name #ty_gn) -> ::core::option::Option<::core::cmp::Ordering> {
                ((*self) as *const (#name #ty_gn)).partial_cmp(&((*other) as *const (#name #ty_gn)))
            }
        }
    };

    expanded.into()
}
