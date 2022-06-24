use engula_api::server::v1::ShardDeleteRequest;

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
use crate::{
    node::{
        engine::{GroupEngine, WriteBatch},
        migrate::ForwardCtx,
        replica::ExecCtx,
    },
    serverpb::v1::{EvalResult, WriteBatchRep},
    Error, Result,
};

pub async fn delete(
    exec_ctx: &ExecCtx,
    group_engine: &GroupEngine,
    req: &ShardDeleteRequest,
) -> Result<EvalResult> {
    let delete = req
        .delete
        .as_ref()
        .ok_or_else(|| Error::InvalidArgument("ShardDeleteRequest::delete is None".into()))?;

    if let Some(migrating_digest) = exec_ctx.migrating_digest.as_ref() {
        if migrating_digest.shard_id == req.shard_id {
            let forward_ctx = ForwardCtx {
                shard_id: migrating_digest.shard_id,
                dest_group_id: migrating_digest.dest_group_id,
                payloads: vec![],
            };
            return Err(Error::Forward(forward_ctx));
        }
    }

    let mut wb = WriteBatch::default();
    group_engine.delete(&mut wb, req.shard_id, &delete.key)?;
    Ok(EvalResult {
        batch: Some(WriteBatchRep {
            data: wb.data().to_owned(),
        }),
        ..Default::default()
    })
}
