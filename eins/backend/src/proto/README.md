# Formally-Verified-E-Voting-Protobufs

Repo für die gRPC Protobufs. Als submodule einbinden

Usage:
Im Backend (in src/proto/proto):
protoc --go_out=. --go_opt=paths=source_relative --go-grpc_out=. --go-grpc_opt=paths=source_relative filename.proto
