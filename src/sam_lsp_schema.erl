% Licensed under the Apache License, Version 2.0 (the "License"); you may not
% use this file except in compliance with the License. You may obtain a copy of
% the License at
%
%   http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing, software
% distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
% WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
% License for the specific language governing permissions and limitations under
% the License.

-module(sam_lsp_schema).


-export([
    client_initiated/0,
    server_initiated/0,
    message_type/1,
    response_type/1,

    cancel_notification/0,
    progress_notification/0,

    work_done_progress_begin_notification/0,
    work_done_progress_report_notification/0,
    work_done_progress_end_notification/0,

    initialize_request/0,
    initialize_response/0,

    initialized_notification/0,

    shutdown_request/0,
    shutdown_response/0,

    exit_notification/0,

    show_message_notification/0,

    show_message_request/0,
    show_message_response/0,

    log_message_notification/0,

    work_done_progress_create_request/0,
    work_done_progress_create_response/0,

    work_done_progress_cancel_notification/0,

    telemetry_notification/0,

    register_capability_request/0,
    register_capability_response/0,

    unregister_capability_request/0,
    unregister_capability_response/0,

    workspace_folders_request/0,
    workspace_folders_response/0,

    did_change_workspace_folders_notification/0,

    did_change_configuration_notification/0,

    configuration_request/0,
    configuration_response/0,

    did_change_watched_files_notification/0,

    workspace_symbol_request/0,
    workspace_symbol_response/0,

    execute_command_request/0,
    execute_command_response/0,

    apply_workspace_edit_request/0,
    apply_workspace_edit_response/0,
    
    did_open_text_document_notification/0,

    did_change_text_document_notification/0,
    
    will_save_text_document_notification/0,

    will_save_wait_until_text_document_request/0,
    will_save_wait_until_text_document_response/0,

    did_save_text_document_notification/0,

    did_close_text_document_notification/0,

    publish_diagnostics_notification/0,

    completion_request/0,
    completion_response/0,

    completion_item_resolve_request/0,
    completion_item_resolve_response/0,

    hover_request/0,
    hover_response/0,

    signature_help_request/0,
    signature_help_response/0,
    
    declaration_request/0,
    declaration_response/0,

    definition_request/0,
    definition_response/0,

    type_definition_request/0,
    type_definition_response/0,

    implementation_request/0,
    implementation_response/0,

    reference_request/0,
    reference_response/0,

    document_highlight_request/0,
    document_highlight_response/0,

    document_symbol_request/0,
    document_symbol_response/0,

    code_action_request/0,
    code_action_response/0,

    code_lens_request/0,
    code_lens_response/0,

    code_lens_resolve_request/0,
    code_lens_resolve_response/0,

    document_link_request/0,
    document_link_response/0,

    document_link_resolve_request/0,
    document_link_resolve_response/0,

    document_color_request/0,
    document_color_response/0,

    color_presentation_request/0,
    color_presentation_response/0,

    document_formatting_request/0,
    document_formatting_response/0,

    document_range_formatting_request/0,
    document_range_formatting_response/0,

    document_on_type_formatting_request/0,
    document_on_type_formatting_response/0,

    rename_request/0,
    rename_response/0,

    prepare_rename_request/0,
    prepare_rename_response/0,
    
    folding_range_request/0,
    folding_range_response/0,

    selection_range_request/0,
    selection_range_response/0
]).


client_initiated() ->
    [
        cancel_notification,
        progress_notification,
        
        work_done_progress_begin_notification,
        work_done_progress_report_notification,
        work_done_progress_end_notification,
        
        initialize_request,
        initialized_notification,
        shutdown_request,  
        exit_notification,

        show_message_response,

        work_done_progress_create_response,
        work_done_progress_cancel_notification,

        register_capability_response,
        unregister_capability_response,
        
        workspace_folders_response,
        
        did_change_workspace_folders_notification,
        did_change_configuration_notification,
        
        configuration_response,
        
        did_change_watched_files_notification,
        
        workspace_symbol_request,
        
        execute_command_request,
        
        apply_workspace_edit_response,
        
        did_open_text_document_notification,
        did_change_text_document_notification,
        
        will_save_text_document_notification,
        
        will_save_wait_until_text_document_request,
        
        did_save_text_document_notification,
        did_close_text_document_notification,
        
        completion_request,
        completion_item_resolve_request,
        hover_request,
        signature_help_request,
        declaration_request,
        definition_request,
        type_definition_request,
        implementation_request,
        reference_request,
        document_highlight_request,
        document_symbol_request,
        code_action_request,
        code_lens_request,
        code_lens_resolve_request,
        document_link_request,
        document_link_resolve_request,
        document_color_request,
        color_presentation_request,
        document_formatting_request,
        document_range_formatting_request,
        document_on_type_formatting_request,
        rename_request,
        prepare_rename_request,
        folding_range_request,
        selection_range_request
    ].

server_initiated() ->
    [
        work_done_progress_report_notification,
        work_done_progress_end_notification,

        initialize_response,

        shutdown_response,
        
        show_message_notification,
        show_message_request,
        
        log_message_notification,

        work_done_progress_create_request,

        telemetry_notification,

        register_capability_request,
        unregister_capability_request,

        workspace_folders_request,
        
        configuration_request,
        
        workspace_symbol_response,
        
        execute_command_response,
        
        apply_workspace_edit_request,
        
        will_save_wait_until_text_document_response,

        publish_diagnostics_notification,
        
        completion_response,
        completion_item_resolve_response,
        hover_response,
        signature_help_response,
        declaration_response,
        definition_response,
        type_definition_response,
        implementation_response,
        reference_response,
        document_highlight_response,
        document_symbol_response,
        code_action_response,
        code_lens_response,
        code_lens_resolve_response,
        document_link_response,
        document_link_resolve_response,
        document_color_response,
        color_presentation_response,
        document_formatting_response,
        document_range_formatting_response,
        document_on_type_formatting_response,
        rename_response,
        prepare_rename_response,
        folding_range_response,
        selection_range_response
    ].

message_type(Body) ->
    case maps:get(<<"id">>, Body, undefined) of
        undefined ->
            notification;
        _Id ->
            case maps:get(<<"method">>, Body, undefined) of
                undefined ->
                    response;
                _Method ->
                    request
            end
    end.

response_type(initialize_request) ->
    initialize_response;
response_type(shutdown_request) ->
    shutdown_response;
response_type(show_message_request) ->
    show_message_response;
response_type(work_done_progress_create_request) ->
    work_done_progress_create_response;
response_type(register_capability_request) ->
    register_capability_response;
response_type(unregister_capability_request) ->
    unregister_capability_response;
response_type(workspace_folders_request) ->
    workspace_folders_response;
response_type(configuration_request) ->
    configuration_response;
response_type(workspace_symbol_request) ->
    workspace_symbol_response;
response_type(apply_workspace_edit_request) ->
    apply_workspace_edit_response;
response_type(execute_command_request) ->
    execute_command_response;
response_type(will_save_wait_until_text_document_request) ->
    will_save_wait_until_text_document_response;
response_type(completion_request) ->
    completion_response;
response_type(completion_item_resolve_request) ->
    completion_item_resolve_response;
response_type(hover_request) ->
    hover_response;
response_type(signature_help_request) ->
    signature_help_response;
response_type(declaration_request) ->
    declaration_response;
response_type(definition_request) ->
    definition_response;
response_type(type_definition_request) ->
    type_definition_response;
response_type(implementation_request) ->
    implementation_response;
response_type(reference_request) ->
    reference_response;
response_type(document_highlight_request) ->
    document_highlight_response;
response_type(document_symbol_request) ->
    document_symbol_response;
response_type(code_action_request) ->
    code_action_response;
response_type(code_lens_request) ->
    code_lens_response;
response_type(code_lens_resolve_request) ->
    code_lens_resolve_response;
response_type(document_link_request) ->
    document_link_response;
response_type(document_link_resolve_request) ->
    document_link_resolve_response;
response_type(document_color_request) ->
    document_color_response;
response_type(color_presentation_request) ->
    color_presentation_response;
response_type(document_formatting_request) ->
    document_formatting_response;
response_type(document_range_formatting_request) ->
    document_range_formatting_response;
response_type(document_on_type_formatting_request) ->
    document_on_type_formatting_response;
response_type(rename_request) ->
    rename_response;
response_type(prepare_rename_request) ->
    prepare_rename_response;
response_type(folding_range_request) ->
    folding_range_response;
response_type(selection_range_request) ->
    selection_range_response;
response_type(_) ->
    undefined.

opt(Type) ->
    {optional, Type}.

array(Type) ->
    {array, Type}.

sized_array(Size, Type) ->
    {array, Size, Type}.

float_range(Low, High) ->
    {float_range, Low, High}.

message() ->
    #{jsonrpc => string}.

request_message() ->
    Base = message(),
    Base#{
        id => [number, string],
        method => string,
        params => opt([array, object])
    }.

response_message() ->
    Base = message(),
    Base#{
        id => [number, string, null],
        result => opt([string, number, boolean, object, null]),
        error => opt(response_error())
    }.

response_error() ->
    #{
        code => number,
        message => string,
        data => opt([string, number, boolean, array, object, null])
    }.

notification_message() ->
    Base = message(),
    Base#{
        method => string,
        params => opt([array, object])
    }.

cancel_notification() ->
    Base = notification_message(),
    Base#{
        params => #{id => [number, string]}
    }.

progress_token() ->
    [number, string].

progress_notification() ->
    Base = notification_message(),
    Base#{
        params => #{
            token => [number, string],
            value => any
        }
    }.

uri() ->
    document_uri.

position() ->
    #{
        line => number,
        character => number
    }.

range() ->
    #{
        start => position(),
        'end' => position()
    }.

location() ->
    #{
        uri => uri(),
        range => range()
    }.

location_link() ->
    #{
        originSelectionRange => opt(range()),
        targetUri => uri(),
        targetRange => range(),
        targetSelectionRange => range()
    }.

diagnostic() ->
    #{
        range => range(),
        severity => opt(diagnostic_severity()),
        code => opt([number, string]),
        source => opt(string),
        message => string,
        tags => opt(array(diagnostic_tag())),
        relatedInformation => opt(array(diagnostic_related_information()))
    }.

diagnostic_severity() ->
    [1, 2, 3,4].

diagnostic_tag() ->
    [1, 2].

diagnostic_related_information() ->
    #{
        location => location(),
        message => string
    }.

command() ->
    #{
        title => string,
        command => string,
        arguments => array(any)
    }.

text_edit() ->
    #{
        range => range(),
        newText => string
    }.

text_document_edit() ->
    #{
        textDocument => versioned_text_document_identifier(),
        edits => array(text_edit())
    }.

create_file_options() ->
    #{
        overwrite => opt(boolean),
        ignoreIfExists => opt(boolean)
    }.

create_file() ->
    #{
        kind => <<"create">>,
        uri => uri(),
        options => opt(create_file_options())
    }.

rename_file_options() ->
    #{
        overwrite => opt(boolean),
        ignoreIfExists => opt(boolean)
    }.

rename_file() ->
    #{
        kind => <<"rename">>,
        oldUri => uri(),
        newUri => uri(),
        options => opt(rename_file_options())
    }.

delete_file_options() ->
    #{
        recursive => opt(boolean),
        ignoreIfNotExists => opt(boolean)
    }.

delete_file() ->
    #{
        kind => <<"delete">>,
        uri => uri(),
        options => opt(delete_file_options())
    }.

workspace_edit() ->
    #{
        changes => opt(#{uri() => array(text_edit())}),
        documentChanges => opt([
            array(text_document_edit()),
            array([text_document_edit(), create_file(), rename_file(), delete_file()])
        ])
    }.

workspace_edit_client_capabilities() ->
    #{
        documentChanges => opt(boolean),
        resourceOperations => opt(resource_operation_kind()),
        failureHandling => opt(failure_handling_kind())
    }.

resource_operation_kind() ->
    [<<"create">>, <<"rename">>, <<"delete">>].

failure_handling_kind() ->
    [<<"abort">>, <<"transactional">>, <<"undo">>, <<"textOnlyTransactional">>].

text_document_identifier() ->
    #{
        uri => uri()
    }.

text_document_item() ->
    #{
        uri => uri(),
        languageId => string,
        version => number,
        text => string
    }.

versioned_text_document_identifier() ->
    #{
        version => [number, null]
    }.

text_document_position_params() ->
    #{
        textDocument => text_document_identifier(),
        position => position()
    }.

document_filter() ->
    #{
        language => opt(string),
        scheme => opt(string),
        pattern => opt(string)
    }.

document_selector() ->
    array(document_filter()).

static_registration_options() ->
    #{
        id => opt(string)
    }.

text_document_registration_options() ->
    #{
        documentSelector => [document_selector(), null]
    }.

markup_kind() ->
    [<<"plaintext">>, <<"markdown">>].

markup_content() ->
    #{
        kind => markup_kind(),
        value => string
    }.

work_done_progress_begin_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"$/progress">>,
        params => work_done_progress_begin()
    }.

work_done_progress_begin() ->
    #{
        kind => <<"begin">>,
        title => string,
        cancellable => opt(boolean),
        message => opt(string),
        percentage => opt(number)
    }.

work_done_progress_report_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"$/progress">>,
        params => work_done_progress_report()
    }.

work_done_progress_report() ->
    #{
        kind => <<"report">>,
        cancellable => opt(boolean),
        message => opt(string),
        percentage => opt(number)
    }.

work_done_progress_end_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"$/progress">>,
        params => work_done_progress_end()
    }.

work_done_progress_end() ->
    #{
        kind => <<"end">>,
        message => opt(string)
    }.

work_done_progress_params() ->
    #{
        workDoneToken => opt(progress_token())
    }.

work_done_progress_options() ->
    #{
        workDoneProgress => opt(boolean)
    }.

partial_result_params() ->
    #{
        partialResultToken => opt(progress_token())
    }.

initialize_request() ->
    Base = request_message(),
    Base#{
        method => <<"initialize">>,
        params => initialize_params()
    }.

initialize_params() ->
    Base = work_done_progress_params(),
    Base#{
        processId => [number, null],
        clientInfo => opt(#{
            name => string,
            version => opt(string)
        }),
        rootPath => opt([string, null]),
        rootUri => [uri(), null],
        initializationOptions => opt(any),
        capabilities => client_capabilities(),
        trace => opt([<<"off">>, <<"messages">>, <<"verbose">>]),
        workspaceFolders => opt([array(workspace_folder()), null])
    }.

text_document_client_capabilities() ->
    #{
        synchronization => opt(text_document_sync_client_capabilities()),
        completion => opt(completion_client_capabilities()),
        hover => opt(hover_client_capabilities()),
        signatureHelp => opt(signature_help_client_capabilities()),
        declaration => opt(declaration_client_capabilities()),
        definition => opt(definition_client_capabilities()),
        typeDefinition => opt(type_definition_client_capabilities()),
        implementation => opt(implementation_client_capabilities()),
        references => opt(reference_client_capabilities()),
        documentHighlight => opt(document_highlight_client_capabilities()),
        documentSymbol => opt(document_symbol_client_capabilities()),
        codeAction => opt(code_action_client_capabilities()),
        codeLens => opt(code_lens_client_capabilities()),
        documentLink => opt(document_link_client_capabilities()),
        colorProvider => opt(document_color_client_capabilities()),
        formatting => opt(document_formatting_client_capabilities()),
        rangeFormatting => opt(document_range_formatting_client_capabilities()),
        onTypeFormatting => opt(document_on_type_formatting_client_capabilities()),
        rename => opt(rename_client_capabilities()),
        publishDiagnostics => opt(publish_diagnostics_client_capabilities()),
        foldingRange => opt(folding_range_client_capabilities()),
        selectionRange => opt(selection_range_client_capabilities())
    }.

client_capabilities() ->
    #{
        workspace => opt(#{
            applyEdit => opt(boolean),
            workspaceEdit => opt(workspace_edit_client_capabilities()),
            didChangeConfiguration => opt(did_change_configuration_client_capabilities()),
            didChangeWatchedFiles => opt(did_change_watched_files_client_capabilities()),
            symbol => opt(workspace_symbol_client_capabilities()),
            executeCommand => opt(execute_command_client_capabilities()),
            workspaceFolderes => opt(boolean),
            configuration => opt(boolean)
        }),
        textDocument => opt(text_document_client_capabilities()),
        window => opt(#{
            workDoneProgress => opt(boolean)
        }),
        experimental => opt(any)
    }.

initialize_response() ->
    Base = response_message(),
    Success = maps:remove(error, Base#{
        result => initialize_result()
    }),
    Error = maps:remove(result, Base#{
        error => #{
            code => 1,
            message => <<"unknown protocol version">>,
            data => #{
                retry => boolean
            }
        }
    }),
    [Success, Error].

initialize_result() ->
    #{
        capabilities => server_capabilities(),
        serverInfo => opt(#{
            name => string,
            version => opt(string)
        })
    }.

server_capabilities() ->
    #{
        textDocumentSync => opt([text_document_sync_options()]),
        completionProvider => opt(completion_options()),
        hoverProvider => opt([boolean, hover_options()]),
        signatureHelpProvider => opt(signature_help_options()),
        declarationProvider => opt([boolean, declaration_options()]),
        definitionProvider => opt([boolean, definition_options()]),
        typeDefinitionProvider => opt([boolean, type_definition_options()]),
        implementationProvider => opt([boolean, implementation_options()]),
        referencesProvider => opt([boolean, reference_options()]),
        documentHighlightProvider => opt([boolean, document_highlight_options()]),
        documentSymbolProvider => opt([boolean, document_symbol_options()]),
        codeActionProvider => opt([boolean, code_action_options()]),
        codeLensProvider => opt(code_lens_options()),
        documentLinkProvider => opt(document_link_options()),
        colorProvider => opt([boolean, document_color_options()]),
        documentFormattingProvider => opt([boolean, document_formatting_options()]),
        documentRangeFormattingProvider => opt([boolean, document_range_formatting_options()]),
        documentOnTypeFormattingProvider => opt(document_on_type_formatting_options()),
        renameProvider => opt([boolean, rename_options()]),
        foldingRangeProvider => opt([boolean, folding_range_options()]),
        executeCommandProvider => opt(execute_command_options()),
        selectionRangeProvider => opt([boolean, selection_range_options()]),
        workspaceSymbolProvider => opt([boolean, workspace_symbol_options()]),
        workspace => opt(#{
            workspaceFolders => opt(workspace_folders_server_capabilities())
        }),
        experimental => opt(any)
    }.

initialized_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"initialized">>,
        params => #{}
    }.

shutdown_request() ->
    Base = request_message(),
    maps:remove(params, Base#{
        method => <<"shutdown">>
    }).

shutdown_response() ->
    Base = response_message(),
    Base#{
        result => null
    }.

exit_notification() ->
    Base = notification_message(),
    maps:remove(params, Base#{
        method => <<"exit">>
    }).

show_message_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"window/showMessage">>,
        params => show_message_params()
    }.

show_message_params() ->
    #{
        type => message_type(),
        message => string
    }.

message_type() ->
    [1, 2, 3, 4].

show_message_request() ->
    Base = request_message(),
    Base#{
        method => <<"window/showMessageRequest">>,
        params => show_message_request_params()
    }.

show_message_request_params() ->
    #{
        type => message_type(),
        message => string,
        actions => opt([message_action_item()])
    }.

message_action_item() ->
    #{
        title => string
    }.

show_message_response() ->
    Base = response_message(),
    Base#{
        result => [message_action_item(), null]
    }.

log_message_notification() ->
    #{
        method => <<"window/logMessage">>,
        params => log_message_params()
    }.

log_message_params() ->
    #{
        type => message_type(),
        message => string
    }.

work_done_progress_create_request() ->
    Base = request_message(),
    Base#{
        method => <<"window/workDoneProgres/create">>,
        params => work_done_progress_create_params()
    }.

work_done_progress_create_params() ->
    #{
        token => progress_token()
    }.

work_done_progress_create_response() ->
    Base = response_message(),
    maps:remove(result, Base).

work_done_progress_cancel_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"window/workDoneProgress/cancel">>,
        params => work_done_progress_cancel_params()
    }.

work_done_progress_cancel_params() ->
    #{
        token => progress_token()
    }.

telemetry_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"telemetry/event">>,
        params => any
    }.

register_capability_request() ->
    Base = request_message(),
    Base#{
        method => <<"client/registerCapability">>,
        params => registration_params()
    }.

registration() ->
    #{
        id => string,
        method => string,
        registrationOptions => [
            text_document_registration_options(),
            did_change_watched_files_registration_options(),
            workspace_symbol_registration_options(),
            execute_command_registration_options(),
            text_document_change_registration_options(),
            text_document_save_registration_options(),
            completion_registration_options(),
            hover_registration_options(),
            signature_help_registration_options(),
            declaration_registration_options(),
            definition_registration_options(),
            type_definition_registration_options(),
            implementation_registration_options(),
            reference_registration_options(),
            document_highlight_registration_options(),
            document_symbol_registration_options(),
            code_action_registration_options(),
            code_lens_registration_options(),
            document_link_registration_options(),
            document_color_registration_options(),
            document_formatting_registration_options(),
            document_range_formatting_registration_options(),
            document_on_type_formatting_registration_options(),
            rename_registration_options(),
            folding_range_registration_options(),
            selection_range_registration_options()
        ]
    }.

registration_params() ->
    #{
        registrations => array(registration())
    }.

register_capability_response() ->
    Base = response_message(),
    maps:remove(result, Base).

unregister_capability_request() ->
    Base = request_message(),
    Base#{
        method => <<"client/unregisterCapability">>,
        params => unregistration_params()
    }.

unregistration() ->
    #{
        id => string,
        method => string
    }.

unregistration_params() ->
    #{
        unregistrations => array(unregistration())
    }.

unregister_capability_response() ->
    Base = response_message(),
    maps:remove(result, Base).

workspace_folders_server_capabilities() ->
    #{
        supported => opt(boolean),
        changeNotifications => opt([string, boolean])
    }.

workspace_folders_request() ->
    Base = request_message(),
    maps:remove(params, Base#{
        method => <<"workspace/workspaceFolders">>
    }).

workspace_folders_response() ->
    Base = response_message(),
    Base#{
        result => [array(workspace_folder()), null]
    }.

workspace_folder() ->
    #{
        uri => uri(),
        name => string
    }.

did_change_workspace_folders_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"workspace/didChangeWorkspaceFolders">>,
        params => did_change_workspace_folders_params()
    }.

did_change_workspace_folders_params() ->
    #{
        event => workspace_folders_change_event()
    }.

workspace_folders_change_event() ->
    #{
        added => array(workspace_folder()),
        removed => array(workspace_folder())
    }.

did_change_configuration_client_capabilities() ->
    #{
        dynamicRegistration => boolean
    }.

did_change_configuration_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"workspace/didChangeConfiguration">>,
        params => did_change_configuration_params()
    }.

did_change_configuration_params() ->
    #{
        settings => any
    }.

configuration_request() ->
    Base = request_message(),
    Base#{
        method => <<"workspace/configuration">>,
        params => configuration_params()
    }.

configuration_params() ->
    #{
        items => array(configuration_item())
    }.

configuration_item() ->
    #{
        scopeUri => opt(uri()),
        section => opt(string)
    }.

configuration_response() ->
    Base = response_message(),
    Base#{
        result => array
    }.

did_change_watched_files_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

did_change_watched_files_registration_options() ->
    #{
        watchers => array(file_system_watcher())
    }.

file_system_watcher() ->
    #{
        globPattern => string,
        kind => opt(watch_kind())
    }.

watch_kind() ->
    [0, 1, 2, 3, 4, 5, 6, 7].

did_change_watched_files_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"workspace/didChangeWatchedFiles">>,
        params => did_change_watched_files_params()
    }.

did_change_watched_files_params() ->
    #{
        changes => array(file_event())
    }.

file_event() ->
    #{
        uri => uri(),
        type => file_change_type()
    }.

file_change_type() ->
    [1, 2, 3].

workspace_symbol_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        symbolKind => opt(#{
            valueSet => opt(array(symbol_kind()))
        })
    }.

workspace_symbol_options() ->
    work_done_progress_options().

workspace_symbol_registration_options() ->
    workspace_symbol_options().

workspace_symbol_request() ->
    Base = request_message(),
    Base#{
        method => <<"workspace/symbol">>,
        params => workspace_symbol_params()
    }.

workspace_symbol_params() ->
    #{
        query => string
    }.

workspace_symbol_response() ->
    Base = response_message(),
    Base#{
        result => [array(symbol_information()), null]
    }.

execute_command_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

execute_command_options() ->
    Base = work_done_progress_options(),
    Base#{
        commands => array(string)
    }.

execute_command_registration_options() ->
    execute_command_options().

execute_command_request() ->
    Base = request_message(),
    Base#{
        method => <<"workspace/executeCommand">>,
        params => execute_command_params()
    }.

execute_command_params() ->
    Base = work_done_progress_params(),
    Base#{
        command => string,
        arguments => opt(array)
    }.

execute_command_response() ->
    Base = response_message(),
    Base#{
        result => [any, null]
    }.

apply_workspace_edit_request() ->
    Base = request_message(),
    Base#{
        method => <<"workspace/applyEdit">>,
        params => apply_workspace_edit_params()
    }.

apply_workspace_edit_params() ->
    #{
        label => opt(string),
        edit => workspace_edit()
    }.

apply_workspace_edit_response() ->
    Base = response_message(),
    Base#{
        result => #{
            applied => boolean,
            failureReason => opt(string)
        }
    }.

text_document_sync_kind() ->
    [0, 1, 2].

text_document_sync_options() ->
    #{
        openClose => opt(boolean),
        change => opt(text_document_sync_kind()),
        willSave => opt(boolean),
        willSaveWaitUntil => opt(boolean),
        save => opt([boolean, save_options()])
    }.

did_open_text_document_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"textDocument/didOpen">>,
        params => did_open_text_document_params()
    }.

did_open_text_document_params() ->
    #{
        textDocument => text_document_item()
    }.

text_document_change_registration_options() ->
    Base = text_document_registration_options(),
    Base#{
        syncKind => text_document_sync_kind()
    }.

did_change_text_document_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"textDocument/didChange">>,
        params => did_change_text_document_params()
    }.

did_change_text_document_params() ->
    #{
        textDocument => versioned_text_document_identifier(),
        contentChanges => array(text_document_content_change_event())
    }.

text_document_content_change_event() ->    
    RangeChange = #{
        range => range(),
        rangeLength => opt(number),
        text => string
    },
    CompleteChange = #{
        text => string
    },
    [RangeChange, CompleteChange].

will_save_text_document_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"textDocument/willSave">>,
        params => will_save_text_document_params()
    }.

will_save_text_document_params() ->
    #{
        textDocument => text_document_identifier(),
        reason => text_document_save_reason()
    }.

text_document_save_reason() ->
    [1, 2, 3].

will_save_wait_until_text_document_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/willSaveWaitUntil">>,
        params => will_save_text_document_params()
    }.

will_save_wait_until_text_document_response() ->
    Base = response_message(),
    Base#{
        result => [array(text_edit()), null]
    }.

save_options() ->
    #{
        includeText => opt(boolean)
    }.

text_document_save_registration_options() ->
    Base = text_document_registration_options(),
    Base#{
        includeText => opt(boolean)
    }.

did_save_text_document_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"textDocument/didSave">>,
        params => did_save_text_document_params()
    }.

did_save_text_document_params() ->
    #{
        textDocument => text_document_identifier(),
        text => opt(string)
    }.

did_close_text_document_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"textDocument/didClose">>,
        params => did_close_text_document_params()
    }.

did_close_text_document_params() ->
    #{
        textDocument => text_document_identifier()
    }.

text_document_sync_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        willSave => opt(boolean),
        willSaveWaitUntil => opt(boolean),
        didSave => opt(boolean)
    }.

publish_diagnostics_client_capabilities() ->
    #{
        relatedInformation => opt(boolean),
        tagSupport => opt(#{
            valueSet => array(diagnostic_tag())
        }),
        versionSupoprt => opt(boolean)
    }.

publish_diagnostics_notification() ->
    Base = notification_message(),
    Base#{
        method => <<"textDocument/publishDiagnostics">>,
        params => publish_diagnostics_params()
    }.

publish_diagnostics_params() ->
    #{
        uri => uri(),
        version => opt(number),
        diagnostics => array(diagnostic())
    }.

completion_client_capabilities() ->
    #{
        dynamicRegistratin => opt(boolean),
        completionItem => opt(#{
            snippetSupport => opt(boolean),
            commitCharactersSupport => opt(boolean),
            documentationFormat => opt(array(markup_kind())),
            deprecatedSupport => opt(boolean),
            preselectSupport => opt(boolean),
            tagSupport => opt(#{
                valueSet => array(completion_item_tag())
            })
        }),
        completionItemKind => opt(#{
            valueSet => opt(array(completion_item_kind()))
        }),
        contextSupport => opt(boolean)
    }.

completion_options() ->
    Base = work_done_progress_options(),
    Base#{
        triggerCharacters => opt(array(string)),
        allCommitCharacters => opt(array(string)),
        resolveProvider => opt(boolean)
    }.

completion_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = completion_options(),
    maps:merge(Base1, Base2).

completion_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/completion">>,
        params => completion_params()
    }.

completion_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base3 = partial_result_params(),
    Base = maps:merge(Base1, maps:merge(Base2, Base3)),
    Base#{
        context => opt(completion_context())
    }.

completion_trigger_kind() ->
    [1, 2, 3].

completion_context() ->
    #{
        triggerKind => completion_trigger_kind(),
        tirggerCharacters => opt(string)
    }.

completion_response() ->
    Base = response_message(),
    Base#{
        result => [array(completion_item()), completion_list(), null]
    }.

completion_list() ->
    #{
        isIncomplete => boolean,
        items => array(completion_item())
    }.

insert_text_format() ->
    [1, 2].

completion_item_tag() ->
    1.

completion_item() ->
    #{
        label => string,
        kind => opt(completion_item_kind()),
        tags => opt(array(completion_item_tag())),
        detail => opt(string),
        documentation => opt([string, markup_content()]),
        deprecated => opt(boolean),
        preselect => opt(boolean),
        sortText => opt(string),
        filterText => opt(string),
        insertText => opt(string),
        insertTextFormat => opt(insert_text_format()),
        textEdit => opt(text_edit()),
        additionalTextEdits => opt(array(text_edit())),
        commitCharacters => opt(array(string)),
        command => opt(command()),
        data => opt(any)
    }.

completion_item_kind() ->
    [
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15,
        16,
        17,
        18,
        19,
        20,
        21,
        22,
        23,
        24,
        25
    ].

completion_item_resolve_request() ->
    Base = request_message(),
    Base#{
        method => <<"completionItem/resolve">>,
        params => completion_item()
    }.

completion_item_resolve_response() ->
    Base = response_message(),
    Base#{
        result => completion_item()
    }.

hover_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        contentFormat => opt(array(markup_kind()))
    }.

hover_options() ->
    work_done_progress_options().

hover_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = hover_options(),
    maps:merge(Base1, Base2).

hover_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/hover">>,
        params => hover_params()
    }.

hover_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    maps:merge(Base1, Base2).

hover_response() ->
    Base = response_message(),
    Base#{
        result => hover_result()
    }.

hover_result() ->
    #{
        contents => [marked_string(), array(marked_string()), markup_content()],
        range => opt(range())
    }.

marked_string() ->
    [string, #{language => string, value => string}].

signature_help_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        signatureInformation => opt(#{
            documentationFormat => opt(array(markup_kind())),
            parameterInformation => opt(#{
                labelOffsetSupport => opt(boolean)
            })
        }),
        contextSupport => opt(boolean)
    }.

signature_help_options() ->
    Base = work_done_progress_options(),
    Base#{
        triggerCharacters => opt(array(string)),
        retriggerCharacters => opt(array(string))
    }.

signature_help_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = signature_help_options(),
    maps:merge(Base1, Base2).

signature_help_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/signatureHelp">>,
        params => signature_help_params()
    }.

signature_help_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        context => opt(signature_help_context())
    }.

signature_help_trigger_kind() ->
    [1, 2, 3].

signature_help_context() ->
    #{
        triggerKind => signature_help_trigger_kind(),
        triggerCharacter => opt(string),
        isRetrigger => boolean,
        activeSignatureHelp => signature_help()
    }.

signature_help_response() ->
    Base = response_message(),
    Base#{
        result => [signature_help(), null]
    }.

signature_help() ->
    #{
        signatures => array(signature_information()),
        activeSignature => opt(number),
        activeParamter => opt(number)
    }.

signature_information() ->
    #{
        label => string,
        documentation => opt([string, markup_content()]),
        parameters => opt(array(parameter_information()))
    }.

parameter_information() ->
    #{
        label => [string, sized_array(2, number)],
        documentation => opt([string, markup_content()])
    }.

declaration_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        linkSupport => opt(boolean)
    }.

declaration_options() ->
    work_done_progress_options().

declaration_registration_options() ->
    Base1 = declaration_options(),
    Base2 = text_document_registration_options(),
    Base3 = static_registration_options(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

declaration_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/declaration">>,
        params => declaration_params()
    }.

declaration_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base3 = partial_result_params(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

declaration_response() ->
    Base = response_message(),
    Base#{
        result => [location(), array(location()), array(location_link())]
    }.

definition_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        linkSupport => opt(boolean)
    }.

definition_options() ->
    work_done_progress_options().

definition_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = definition_options(),
    maps:merge(Base1, Base2).

definition_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/definition">>,
        params => definition_params()
    }.

definition_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base3 = partial_result_params(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

definition_response() ->
    Base = response_message(),
    Base#{
        result => [location(), array(location()), array(location_link())]
    }.

type_definition_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        linkSupport => opt(boolean)
    }.

type_definition_options() ->
    work_done_progress_options().

type_definition_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = type_definition_options(),
    Base3 = static_registration_options(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

type_definition_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/typeDefinition">>,
        params => type_definition_params()
    }.

type_definition_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base3 = partial_result_params(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

type_definition_response() ->
    Base = response_message(),
    Base#{
        result => [location(), array(location()), array(location_link())]
    }.

implementation_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        linkSupport => opt(boolean)
    }.

implementation_options() ->
    work_done_progress_options().

implementation_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = implementation_options(),
    Base3 = static_registration_options(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

implementation_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/implementation">>,
        params => implementation_params()
    }.

implementation_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base3 = partial_result_params(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

implementation_response() ->
    Base = response_message(),
    Base#{
        result => [location(), array(location()), array(location_link())]
    }.

reference_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

reference_options() ->
    work_done_progress_options().

reference_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = reference_options(),
    maps:merge(Base1, Base2).

reference_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/referenes">>,
        params => reference_params()
    }.

reference_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base3 = partial_result_params(),
    Base = maps:merge(Base1, maps:merge(Base2, Base3)),
    Base#{
        context => reference_context()
    }.

reference_context() ->
    #{
        includeDeclaration => boolean
    }.

reference_response() ->
    Base = response_message(),
    Base#{
        result => [array(location()), null]
    }.

document_highlight_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

document_highlight_options() ->
    work_done_progress_options().

document_highlight_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = document_highlight_options(),
    maps:merge(Base1, Base2).

document_highlight_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/documentHighlight">>,
        params => document_highlight_params()
    }.

document_highlight_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base3 = partial_result_params(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

document_highlight_response() ->
    Base = response_message(),
    Base#{
        result => [array(document_highlight()), null]
    }.

document_highlight() ->
    #{
        range => range(),
        kind => opt(document_highlight_kind())
    }.

document_highlight_kind() ->
    [1, 2, 3].

document_symbol_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        symbolKind => opt(#{
            valueSet => opt(symbol_kind())
        }),
        hierarchicalDocumentSymbolSupport => opt(boolean)
    }.

document_symbol_options() ->
    work_done_progress_options().

document_symbol_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = document_symbol_options(),
    maps:merge(Base1, Base2).

document_symbol_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/documentSymbols">>,
        params => document_symbol_params()
    }.

document_symbol_params() ->
    Base1 = work_done_progress_params(),
    Base2 = partial_result_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        textDocument => text_document_identifier()
    }.

document_symbol_response() ->
    Base = response_message(),
    Base#{
        result => [array(document_symbol()), array(symbol_information()), null]
    }.

symbol_kind() ->
    [
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        0,
        10,
        11,
        12,
        13,
        14,
        15,
        16,
        17,
        18,
        19,
        20,
        21,
        22,
        23,
        24,
        25,
        26
    ].

document_symbol() ->
    {recursive, #{
        name => string,
        detail => opt(string),
        kind => symbol_kind(),
        deprecated => opt(boolean),
        range => range(),
        selectionRange => range(),
        children => opt(array(recurse))
    }}.

symbol_information() ->
    #{
        name => string,
        kind => symbol_kind(),
        deprecated => opt(boolean),
        location => location(),
        containerName => opt(string)
    }.

code_action_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        codeActionLiteralSupport => opt(#{
            codeActionKind => #{
                valueSet => array(code_action_kind())
            }
        }),
        isPreferredSupport => opt(boolean)
    }.

code_action_options() ->
    Base = work_done_progress_options(),
    Base#{
        codeActionKinds => opt(array(code_action_kind()))
    }.

code_action_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = code_action_options(),
    maps:merge(Base1, Base2).

code_action_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/codeAction">>,
        params => code_action_params()
    }.

code_action_params() ->
    Base1 = work_done_progress_params(),
    Base2 = partial_result_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        textDocument => text_document_identifier(),
        range => range(),
        context => code_action_context()
    }.

code_action_kind() ->
    [
        <<"">>,
        <<"quickfix">>,
        <<"refactor">>,
        <<"refactor.extract">>,
        <<"refactor.inline">>,
        <<"refactor.rewrite">>,
        <<"source.organizeImports">>,
        string
    ].

code_action_context() ->
    #{
        diagnostics => array(diagnostic()),
        only => opt(array(code_action_kind()))
    }.

code_action_response() ->
    Base = response_message(),
    Base#{
        result => [array([command(), code_action()]), null]
    }.

code_action() ->
    #{
        title => string,
        kind => opt(code_action_kind()),
        diagnostics => opt(array(diagnostic())),
        isPreferred => opt(boolean),
        edit => opt(workspace_edit()),
        command => opt(command())
    }.

code_lens_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

code_lens_options() ->
    Base = work_done_progress_options(),
    Base#{
        resolveProvider => opt(boolean)
    }.

code_lens_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = code_lens_options(),
    maps:merge(Base1, Base2).

code_lens_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/codeLens">>,
        params => code_lens_params()
    }.

code_lens_params() ->
    Base1 = work_done_progress_params(),
    Base2 = partial_result_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        textDocument => text_document_identifier()
    }.

code_lens_response() ->
    Base = response_message(),
    Base#{
        result => [array(code_lens()), null]
    }.

code_lens() ->
    #{
        range => range(),
        command => opt(command()),
        data => opt(any)
    }.

code_lens_resolve_request() ->
    Base = request_message(),
    Base#{
        method => <<"codeLens/resolve">>,
        params => code_lens()
    }.

code_lens_resolve_response() ->
    Base = response_message(),
    Base#{
        result => code_lens()
    }.

document_link_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        tooltipSupport => opt(boolean)
    }.

document_link_options() ->
    Base = work_done_progress_options(),
    Base#{
        resolveProvider => opt(boolean)
    }.

document_link_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = document_link_options(),
    maps:merge(Base1, Base2).

document_link_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/documentLink">>,
        params => document_link_params()
    }.

document_link_params() ->
    Base1 = work_done_progress_params(),
    Base2 = partial_result_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        textDocument => text_document_identifier()
    }.

document_link_response() ->
    Base = response_message(),
    Base#{
        result => [array(document_link()), null]
    }.

document_link() ->
    #{
        range => range(),
        target => opt(uri()),
        tooltip => opt(string),
        data => opt(any)
    }.

document_link_resolve_request() ->
    Base = request_message(),
    Base#{
        method => <<"documentLink/resolve">>,
        params => document_link()
    }.

document_link_resolve_response() ->
    Base = response_message(),
    Base#{
        result => document_link()
    }.

document_color_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

document_color_options() ->
    work_done_progress_options().

document_color_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = document_color_options(),
    maps:merge(Base1, Base2).

document_color_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/documentColor">>,
        params => document_color_params()
    }.

document_color_params() ->
    Base1 = work_done_progress_params(),
    Base2 = partial_result_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        textDocument => text_document_identifier()
    }.

document_color_response() ->
    Base = response_message(),
    Base#{
        result => array(color_information())
    }.

color_information() ->
    #{
        range => range(),
        color => color()
    }.

color() ->
    #{
        red => float_range(0, 1),
        green => float_range(0, 1),
        blue => float_range(0, 1),
        alpha => float_range(0, 1)
    }.

color_presentation_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/colorPresentation">>,
        params => color_presentation_params()
    }.

color_presentation_params() ->
    Base1 = work_done_progress_params(),
    Base2 = partial_result_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        textDocument => text_document_identifier(),
        color => color(),
        range => range()
    }.

color_presentation_response() ->
    Base = response_message(),
    Base#{
        result => array(color_presentation())
    }.

color_presentation() ->
    #{
        label => string,
        textEdit => opt(text_edit()),
        additionalTextEdits => opt(array(text_edit()))
    }.

document_formatting_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

document_formatting_options() ->
    work_done_progress_options().

document_formatting_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = document_formatting_options(),
    maps:merge(Base1, Base2).

document_formatting_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/formatting">>,
        params => document_formatting_params()
    }.

document_formatting_params() ->
    Base = work_done_progress_params(),
    Base#{
        textDocument => text_document_identifier(),
        options => formatting_options()
    }.

formatting_options() ->
    #{
        tabSize => number,
        insertSpaces => boolean,
        timTrailingWhitespace => opt(boolean),
        insertFinalNewLine => opt(boolean),
        trimFinalNewLines => opt(boolean),
        '_' => [boolean, number, string]
    }.

document_formatting_response() ->
    Base = response_message(),
    Base#{
        result => [array(text_edit()), null]
    }.

document_range_formatting_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

document_range_formatting_options() ->
    work_done_progress_options().

document_range_formatting_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = document_range_formatting_options(),
    maps:merge(Base1, Base2).

document_range_formatting_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/rangeFormatting">>,
        params => document_range_formatting_params()
    }.

document_range_formatting_params() ->
    Base = work_done_progress_params(),
    Base#{
        textDocument => text_document_identifier(),
        range => range(),
        options => formatting_options()
    }.

document_range_formatting_response() ->
    Base = response_message(),
    Base#{
        result => [array(text_edit()), null]
    }.

document_on_type_formatting_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

document_on_type_formatting_options() ->
    #{
        firstTriggerCharacter => string,
        moreTriggerCharacters => opt(array(string))
    }.

document_on_type_formatting_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = document_on_type_formatting_options(),
    maps:merge(Base1, Base2).

document_on_type_formatting_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/onTypeFormatting">>,
        parmas => document_on_type_formatting_params()
    }.

document_on_type_formatting_params() ->
    Base = text_document_position_params(),
    Base#{
        ch => string,
        options => formatting_options()
    }.

document_on_type_formatting_response() ->
    Base = response_message(),
    Base#{
        result => [array(text_edit()), null]
    }.

rename_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        prepareSupport => opt(boolean)
    }.

rename_options() ->
    Base = work_done_progress_options(),
    Base#{
        prepareProvider => opt(boolean)
    }.

rename_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = rename_options(),
    maps:merge(Base1, Base2).

rename_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/rename">>,
        params => rename_params()
    }.

rename_params() ->
    Base1 = text_document_position_params(),
    Base2 = work_done_progress_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        newName => string
    }.

rename_response() ->
    Base = response_message(),
    Base#{
        result => [workspace_edit(), null]
    }.

prepare_rename_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/prepareRename">>,
        params => prepare_rename_params()
    }.

prepare_rename_params() ->
    text_document_position_params().

prepare_rename_response() ->
    Base = response_message(),
    Base#{
        result => [
            range(),
            #{
                range => range(),
                placeholder => string
            },
            null
        ]
    }.

folding_range_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean),
        rangeLimit => opt(number),
        lineFoldingOnly => opt(boolean)
    }.

folding_range_options() ->
    work_done_progress_options().

folding_range_registration_options() ->
    Base1 = text_document_registration_options(),
    Base2 = folding_range_options(),
    Base3 = static_registration_options(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

folding_range_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/foldingRange">>,
        params => folding_range_params()
    }.

folding_range_params() ->
    Base1 = work_done_progress_params(),
    Base2 = partial_result_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        textDocument => text_document_identifier()
    }.

folding_range_response() ->
    Base = response_message(),
    Base#{
        result => [array(folding_range()), null]
    }.

folding_range_kind() ->
    [<<"comment">>, <<"imports">>, <<"region">>].

folding_range() ->
    #{
        startLine => number,
        startCharacter => opt(number),
        endLine => number,
        endCharacter => opt(number),
        kind => folding_range_kind()
    }.

selection_range_client_capabilities() ->
    #{
        dynamicRegistration => opt(boolean)
    }.

selection_range_options() ->
    work_done_progress_options().

selection_range_registration_options() ->
    Base1 = selection_range_options(),
    Base2 = text_document_registration_options(),
    Base3 = static_registration_options(),
    maps:merge(Base1, maps:merge(Base2, Base3)).

selection_range_request() ->
    Base = request_message(),
    Base#{
        method => <<"textDocument/selectionRange">>,
        params => selection_range_params()
    }.

selection_range_params() ->
    Base1 = work_done_progress_params(),
    Base2 = partial_result_params(),
    Base = maps:merge(Base1, Base2),
    Base#{
        textDocument => text_document_identifier(),
        positions => array(position())
    }.

selection_range_response() ->
    Base = response_message(),
    Base#{
        result => [array(selection_range()), null]
    }.

selection_range() ->
    {recursive, #{
        range => range(),
        parent => opt(recurse)
    }}.
