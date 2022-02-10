// Copyright 2022 The Engula Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use engula_apis::*;

pub fn get() -> CallExpr {
    CallExpr {
        function: Some(call_expr::Function::Generic(GenericFunction::Get as i32)),
        ..Default::default()
    }
}

pub fn set(v: impl Into<GenericValue>) -> CallExpr {
    CallExpr {
        function: Some(call_expr::Function::Generic(GenericFunction::Set as i32)),
        arguments: vec![v.into()],
    }
}

pub fn delete() -> CallExpr {
    CallExpr {
        function: Some(call_expr::Function::Generic(GenericFunction::Delete as i32)),
        ..Default::default()
    }
}

pub fn add(v: impl Into<GenericValue>) -> CallExpr {
    CallExpr {
        function: Some(call_expr::Function::Numeric(NumericFunction::Add as i32)),
        arguments: vec![v.into()],
    }
}
