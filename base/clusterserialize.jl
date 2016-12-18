# This file is a part of Julia. License is MIT: http://julialang.org/license

import .Serializer: known_object_data, object_number, serialize_cycle, deserialize_cycle, writetag,
                      __deserialized_types__, serialize_typename, deserialize_typename,
                      TYPENAME_TAG, object_numbers

type ClusterSerializer{I<:IO} <: AbstractSerializer
    io::I
    counter::Int
    table::ObjectIdDict

    pid::Int                  # Worker we are connected to.
    sent_objects::Set{UInt64} # used by serialize (track objects sent)
    sent_globals::Dict
    glbs_in_tname::Dict       # A dict tracking globals referenced in anonymous
                              # functions.
    anonfunc_id::UInt64

    ClusterSerializer(io::I) = new(io, 0, ObjectIdDict(),
                                Base.worker_id_from_socket(io),
                                Set{UInt64}(), Dict(), Dict(), 0)
end
ClusterSerializer(io::IO) = ClusterSerializer{typeof(io)}(io)

function deserialize(s::ClusterSerializer, ::Type{TypeName})
    full_body_sent = deserialize(s)
    number = read(s.io, UInt64)
    if !full_body_sent
        tn = get(known_object_data, number, nothing)::TypeName
        if !haskey(object_numbers, tn)
            # set up reverse mapping for serialize
            object_numbers[tn] = number
        end
        deserialize_cycle(s, tn)
    else
        tn = deserialize_typename(s, number)
    end

    # retrieve arrays of global syms sent if any and deserialize them all.
    foreach(sym->deserialize_global_from_main(s, sym), deserialize(s))
    return tn
end

function serialize(s::ClusterSerializer, t::TypeName)
    serialize_cycle(s, t) && return
    writetag(s.io, TYPENAME_TAG)

    identifier = object_number(t)
    send_whole = !(identifier in s.sent_objects)
    serialize(s, send_whole)
    write(s.io, identifier)
    if send_whole
        # Track globals referenced in this anonymous function.
        # This information is used to resend modified globals when we
        # only send the identifier.
        prev = s.anonfunc_id
        s.anonfunc_id = identifier
        serialize_typename(s, t)
        s.anonfunc_id = prev
        push!(s.sent_objects, identifier)
        finalizer(t, x->cleanup_tname_glbs(s, identifier))
    end

    # Send global refs if required.
    syms = syms_2b_sent(s, identifier)
    serialize(s, syms)
    foreach(sym->serialize_global_from_main(s, sym), syms)
    nothing
end

function serialize(s::ClusterSerializer, g::GlobalRef)
    # Record if required and then invoke the default GlobalRef serializer.
    sym = g.name
    if g.mod === Main && isdefined(g.mod, sym)
        v = getfield(Main, sym)
        if  !isa(v, DataType) && !isa(v, Module) &&
            (sym in names(Main, false, false)) && (s.anonfunc_id != 0)
            # FIXME : There must be a better way to detect if a binding has been imported
            # into Main or has been primarily defined here.
            push!(get!(s.glbs_in_tname, s.anonfunc_id, []), sym)
        end
    end

    invoke(serialize, (AbstractSerializer, GlobalRef), s, g)
end

# Send/resend a global object if
# a) has not been sent previously, i.e., we are seeing this object_id for the first time, or,
# b) hash value has changed or
# c) is a bitstype
function syms_2b_sent(s::ClusterSerializer, identifier)
    lst=Symbol[]
    check_syms = get(s.glbs_in_tname, identifier, [])
    for sym in check_syms
        v = getfield(Main, sym)

        if isbits(v)
            push!(lst, sym)
        else
            oid = object_id(v)
            if haskey(s.sent_globals, oid)
                # We have sent this object before, see if it has changed.
                s.sent_globals[oid] != hash(v) && push!(lst, sym)
            else
                push!(lst, sym)
            end
        end
    end
    return unique(lst)
end

function serialize_global_from_main(s::ClusterSerializer, sym)
    v = getfield(Main, sym)

    oid = object_id(v)
    record_v = true
    if isbits(v)
        record_v = false
    elseif !haskey(s.sent_globals, oid)
        # set up a finalizer the first time this object is sent
        try
            finalizer(v, x->delete_global_tracker(s,x))
        catch ex
            # Do not track objects that cannot be finalized.
            record_v = false
        end
    end
    record_v && (s.sent_globals[oid] = hash(v))

    serialize(s, isconst(Main, sym))
    serialize(s, v)
end

function deserialize_global_from_main(s::ClusterSerializer, sym)
    sym_isconst = deserialize(s)
    v = deserialize(s)
    if sym_isconst
        eval(Main, :(const $sym = $v))
    else
        eval(Main, :($sym = $v))
    end
end

function delete_global_tracker(s::ClusterSerializer, v)
    oid = object_id(v)
    if haskey(s.sent_globals, oid)
        delete!(s.sent_globals, oid)
    end

    # TODO: Should release memory from the remote nodes.
end

function cleanup_tname_glbs(s::ClusterSerializer, identifier)
    delete!(s.glbs_in_tname, identifier)
end

# TODO: cleanup from s.sent_objects
